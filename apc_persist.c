/*
  +----------------------------------------------------------------------+
  | APCu                                                                 |
  +----------------------------------------------------------------------+
  | Copyright (c) 2018 The PHP Group                                     |
  +----------------------------------------------------------------------+
  | This source file is subject to version 3.01 of the PHP license,      |
  | that is bundled with this package in the file LICENSE, and is        |
  | available through the world-wide-web at the following url:           |
  | http://www.php.net/license/3_01.txt                                  |
  | If you did not receive a copy of the PHP license and are unable to   |
  | obtain it through the world-wide-web, please send a note to          |
  | license@php.net so we can mail you a copy immediately.               |
  +----------------------------------------------------------------------+
  | Author: Nikita Popov <nikic@php.net>                                 |
  +----------------------------------------------------------------------+
 */

#include "apc.h"
#include "apc_cache.h"

#if PHP_VERSION_ID < 70300
# define GC_SET_REFCOUNT(ref, rc) (GC_REFCOUNT(ref) = (rc))
# define GC_ADDREF(ref) GC_REFCOUNT(ref)++
# define GC_SET_PERSISTENT_TYPE(ref, type) (GC_TYPE_INFO(ref) = type)
# if PHP_VERSION_ID < 70200
#  define GC_ARRAY IS_ARRAY
# else
#  define GC_ARRAY (IS_ARRAY | (GC_COLLECTABLE << GC_FLAGS_SHIFT))
# endif
#else
# define GC_SET_PERSISTENT_TYPE(ref, type) \
	(GC_TYPE_INFO(ref) = type | (GC_PERSISTENT << GC_FLAGS_SHIFT))
#endif

#if PHP_VERSION_ID < 80000
# define GC_REFERENCE IS_REFERENCE
#endif

/*
 * PERSIST: Copy from request memory to SHM.
 */

typedef struct _apc_persist_context_t {
	/* Serializer to use */
	apc_serializer_t *serializer;
	/* Computed size of the needed SMA allocation */
	size_t size;
	/* Whether or not we may have to memoize refcounted addresses */
	zend_bool memoization_needed;
	/* Whether to serialize the top-level value */
	zend_bool use_serialization;
	/* Serialized object/array string, in case there can only be one */
	unsigned char *serialized_str;
	size_t serialized_str_len;
	/* Address (process local) of entry in shm / Whole SMA allocation */
	char *alloc;
	/* Current position in allocation */
	char *alloc_cur;
	/* HashTable storing refcounteds for which the size has already been counted. */
	HashTable already_counted;
	/* HashTable storing already allocated refcounteds. Pointers to refcounteds are stored. */
	HashTable already_allocated;
} apc_persist_context_t;

#define ADD_SIZE(sz) ctxt->size += ZEND_MM_ALIGNED_SIZE(sz)
#define ADD_SIZE_STR(len) ADD_SIZE(_ZSTR_STRUCT_SIZE(len))

#define ALLOC(sz) apc_persist_alloc(ctxt, sz)
#define COPY(val, sz) apc_persist_alloc_copy(ctxt, val, sz)

/* TO_OFF() converts a (process local) pointer from an entry (in shm) to an
 * offset relative to the beginning of this entry. It expects the presence
 * of a variable ctxt that points to an apc_persist_context_t. */
#define TO_OFF(ptr) (apc_persist_compute_offset(ptr, ctxt))

static zend_bool apc_persist_calc_zval(apc_persist_context_t *ctxt, const zval *zv);
static void apc_persist_copy_zval_impl(apc_persist_context_t *ctxt, zval *zv);

static inline void *apc_persist_compute_offset(void *ptr, apc_persist_context_t *ctxt) {
	/* The pointer must point to the shm area of the entry to be persisted */
	assert(((uintptr_t)ptr >= (uintptr_t)ctxt->alloc) && ((uintptr_t)ptr < ((uintptr_t)ctxt->alloc + (uintptr_t)ctxt->size)));

	return ((void *)((uintptr_t)ptr - (uintptr_t)ctxt->alloc));
}

/* Used to reduce hash collisions when using pointers in hash tables. (#175) */
static inline zend_ulong apc_shr3(zend_ulong index) {
	return (index >> 3) | (index << (SIZEOF_ZEND_LONG * 8 - 3));
}

static inline void apc_persist_copy_zval(apc_persist_context_t *ctxt, zval *zv) {
	/* No data apart from the zval itself */
	if (Z_TYPE_P(zv) < IS_STRING) {
		return;
	}

	apc_persist_copy_zval_impl(ctxt, zv);
	Z_PTR_P(zv) = TO_OFF(Z_PTR_P(zv));
}

static void apc_persist_init_context(apc_persist_context_t *ctxt, apc_serializer_t *serializer) {
	ctxt->serializer = serializer;
	ctxt->size = 0;
	ctxt->memoization_needed = 0;
	ctxt->use_serialization = 0;
	ctxt->serialized_str = NULL;
	ctxt->serialized_str_len = 0;
	ctxt->alloc = NULL;
	ctxt->alloc_cur = NULL;
}

static void apc_persist_destroy_context(apc_persist_context_t *ctxt) {
	if (ctxt->memoization_needed) {
		zend_hash_destroy(&ctxt->already_counted);
		zend_hash_destroy(&ctxt->already_allocated);
	}
	if (ctxt->serialized_str) {
		efree(ctxt->serialized_str);
	}
}

static zend_bool apc_persist_calc_memoize(apc_persist_context_t *ctxt, void *ptr) {
	zval tmp;
	zend_ulong key;
	if (!ctxt->memoization_needed) {
		return 0;
	}

	key = apc_shr3((zend_ulong)(uintptr_t) ptr);
	if (zend_hash_index_exists(&ctxt->already_counted, key)) {
		return 1;
	}

	ZVAL_NULL(&tmp);
	zend_hash_index_add_new(&ctxt->already_counted, key, &tmp);
	return 0;
}

static zend_bool apc_persist_calc_ht(apc_persist_context_t *ctxt, const HashTable *ht) {
	uint32_t idx;

	/* In php 7.3+, this points to the immutable zend_empty_array outside of shared memory. */
	if (ht->nNumOfElements == 0) {
#if PHP_VERSION_ID < 70300
		ADD_SIZE(sizeof(HashTable));
#endif
		return 1;
	}
	ADD_SIZE(sizeof(HashTable));

	/* TODO Too sparse hashtables could be compacted here */
#if PHP_VERSION_ID >= 80200
	if (HT_IS_PACKED(ht)) {
		ADD_SIZE(HT_PACKED_USED_SIZE(ht));
		for (idx = 0; idx < ht->nNumUsed; idx++) {
			zval *val = ht->arPacked + idx;
			ZEND_ASSERT(Z_TYPE_P(val) != IS_INDIRECT && "INDIRECT in packed array?");
			if (!apc_persist_calc_zval(ctxt, val)) {
				return 0;
			}
		}
	} else
#endif
	{
		ADD_SIZE(HT_USED_SIZE(ht));
		for (idx = 0; idx < ht->nNumUsed; idx++) {
			Bucket *p = ht->arData + idx;
			if (Z_TYPE(p->val) == IS_UNDEF) continue;

			/* This can only happen if $GLOBALS is placed in the cache.
			 * Don't bother with this edge-case, fall back to serialization. */
			if (Z_TYPE(p->val) == IS_INDIRECT) {
				ctxt->use_serialization = 1;
				return 0;
			}

			/* TODO These strings can be reused
			if (p->key && !apc_persist_calc_is_handled(ctxt, (zend_refcounted *) p->key)) {
				ADD_SIZE_STR(ZSTR_LEN(p->key));
			}*/
			if (p->key) {
				ADD_SIZE_STR(ZSTR_LEN(p->key));
			}
			if (!apc_persist_calc_zval(ctxt, &p->val)) {
				return 0;
			}
		}
	}

	return 1;
}

static zend_bool apc_persist_calc_serialize(apc_persist_context_t *ctxt, const zval *zv) {
	unsigned char *buf = NULL;
	size_t buf_len = 0;

	apc_serialize_t serialize = APC_SERIALIZER_NAME(php);
	void *config = NULL;
	if (ctxt->serializer) {
		serialize = ctxt->serializer->serialize;
		config = ctxt->serializer->config;
	}

	if (!serialize(&buf, &buf_len, zv, config)) {
		return 0;
	}

	/* We only ever serialize the top-level value, memoization cannot be needed */
	ZEND_ASSERT(!ctxt->memoization_needed);
	ctxt->serialized_str = buf;
	ctxt->serialized_str_len = buf_len;

	ADD_SIZE_STR(buf_len);
	return 1;
}

static zend_bool apc_persist_calc_zval(apc_persist_context_t *ctxt, const zval *zv) {
	if (Z_TYPE_P(zv) < IS_STRING) {
		/* No data apart from the zval itself */
		return 1;
	}

	if (ctxt->use_serialization) {
		return apc_persist_calc_serialize(ctxt, zv);
	}

	if (apc_persist_calc_memoize(ctxt, Z_COUNTED_P(zv))) {
		return 1;
	}

	switch (Z_TYPE_P(zv)) {
		case IS_STRING:
			ADD_SIZE_STR(Z_STRLEN_P(zv));
			return 1;
		case IS_ARRAY:
			return apc_persist_calc_ht(ctxt, Z_ARRVAL_P(zv));
		case IS_REFERENCE:
			ADD_SIZE(sizeof(zend_reference));
			return apc_persist_calc_zval(ctxt, Z_REFVAL_P(zv));
		case IS_OBJECT:
			ctxt->use_serialization = 1;
			return 0;
		case IS_RESOURCE:
			apc_warning("Cannot store resources in apcu cache");
			return 0;
		EMPTY_SWITCH_DEFAULT_CASE()
	}
}

static zend_bool apc_persist_calc(apc_persist_context_t *ctxt, const zend_string *key, const zval *zv) {
	ADD_SIZE(APC_ENTRY_SIZE(ZSTR_LEN(key)));

	return apc_persist_calc_zval(ctxt, zv);
}

static inline void *apc_persist_get_already_allocated(apc_persist_context_t *ctxt, void *ptr) {
	if (ctxt->memoization_needed) {
		return zend_hash_index_find_ptr(&ctxt->already_allocated, (uintptr_t) ptr);
	}
	return NULL;
}

static inline void apc_persist_add_already_allocated(
		apc_persist_context_t *ctxt, const void *old_ptr, void *new_ptr) {
	if (ctxt->memoization_needed) {
		zend_hash_index_add_new_ptr(&ctxt->already_allocated, (uintptr_t) old_ptr, new_ptr);
	}
}

static inline void *apc_persist_alloc(apc_persist_context_t *ctxt, size_t size) {
	void *ptr = ctxt->alloc_cur;
	ctxt->alloc_cur += ZEND_MM_ALIGNED_SIZE(size);
	ZEND_ASSERT(ctxt->alloc_cur <= ctxt->alloc + ctxt->size);
	return ptr;
}

static inline void *apc_persist_alloc_copy(
		apc_persist_context_t *ctxt, const void *val, size_t size) {
	void *ptr = apc_persist_alloc(ctxt, size);
	memcpy(ptr, val, size);
	return ptr;
}

static zend_string *apc_persist_copy_cstr(
		apc_persist_context_t *ctxt, const char *orig_buf, size_t buf_len, zend_ulong hash) {
	zend_string *str = ALLOC(_ZSTR_STRUCT_SIZE(buf_len));

	GC_SET_REFCOUNT(str, 1);
	GC_SET_PERSISTENT_TYPE(str, IS_STRING);

	ZSTR_H(str) = hash;
	ZSTR_LEN(str) = buf_len;
	memcpy(ZSTR_VAL(str), orig_buf, buf_len);
	ZSTR_VAL(str)[buf_len] = '\0';
	zend_string_hash_val(str);

	return str;
}

static zend_string *apc_persist_copy_zstr_no_add(
		apc_persist_context_t *ctxt, const zend_string *orig_str) {
	return apc_persist_copy_cstr(
		ctxt, ZSTR_VAL(orig_str), ZSTR_LEN(orig_str), ZSTR_H(orig_str));
}

static inline zend_string *apc_persist_copy_zstr(
		apc_persist_context_t *ctxt, const zend_string *orig_str) {
	zend_string *str = apc_persist_copy_zstr_no_add(ctxt, orig_str);
	apc_persist_add_already_allocated(ctxt, orig_str, str);
	return str;
}

static zend_reference *apc_persist_copy_ref(
		apc_persist_context_t *ctxt, const zend_reference *orig_ref) {
	zend_reference *ref = ALLOC(sizeof(zend_reference));
	apc_persist_add_already_allocated(ctxt, orig_ref, ref);

	GC_SET_REFCOUNT(ref, 1);
	GC_SET_PERSISTENT_TYPE(ref, GC_REFERENCE);
#if PHP_VERSION_ID >= 70400
	ref->sources.ptr = NULL;
#endif

	ZVAL_COPY_VALUE(&ref->val, &orig_ref->val);
	apc_persist_copy_zval(ctxt, &ref->val);

	return ref;
}

static const uint32_t uninitialized_bucket[-HT_MIN_MASK] = {HT_INVALID_IDX, HT_INVALID_IDX};

static zend_array *apc_persist_copy_ht(apc_persist_context_t *ctxt, const HashTable *orig_ht) {
#if PHP_VERSION_ID >= 70300
	if (orig_ht->nNumOfElements == 0) {
		/* To indicate using zend_empty_array during unpersist, we point to the entry's starting address. */
		return (HashTable *)ctxt->alloc;
	}
#endif
	HashTable *ht = COPY(orig_ht, sizeof(HashTable));
	uint32_t idx;
	apc_persist_add_already_allocated(ctxt, orig_ht, ht);

	GC_SET_REFCOUNT(ht, 1);
	GC_SET_PERSISTENT_TYPE(ht, GC_ARRAY);

	/* Immutable arrays from opcache may lack a dtor and the apply protection flag. */
	ht->pDestructor = ZVAL_PTR_DTOR;
#if PHP_VERSION_ID < 70300
	ht->u.flags |= HASH_FLAG_APPLY_PROTECTION;
#endif

	ht->u.flags |= HASH_FLAG_STATIC_KEYS;
	if (ht->nNumUsed == 0) {
#if PHP_VERSION_ID >= 70400
		ht->u.flags = HASH_FLAG_UNINITIALIZED;
#else
		ht->u.flags &= ~(HASH_FLAG_INITIALIZED|HASH_FLAG_PACKED);
#endif
		ht->nNextFreeElement = 0;
		ht->nTableMask = HT_MIN_MASK;
		HT_SET_DATA_ADDR(ht, &uninitialized_bucket);
		return ht;
	}

	ht->nNextFreeElement = 0;
	ht->nInternalPointer = HT_INVALID_IDX;
#if PHP_VERSION_ID >= 80200
	if (HT_IS_PACKED(ht)) {
		HT_SET_DATA_ADDR(ht, COPY(HT_GET_DATA_ADDR(ht), HT_PACKED_USED_SIZE(ht)));
		for (idx = 0; idx < ht->nNumUsed; idx++) {
			zval *val = ht->arPacked + idx;
			if (Z_TYPE_P(val) == IS_UNDEF) continue;

			if (ht->nInternalPointer == HT_INVALID_IDX) {
				ht->nInternalPointer = idx;
			}

			if ((zend_long) idx >= (zend_long) ht->nNextFreeElement) {
				ht->nNextFreeElement = idx + 1;
			}

			apc_persist_copy_zval(ctxt, val);
		}

		ht->arPacked = TO_OFF(ht->arPacked);
	} else
#endif
	{
		HT_SET_DATA_ADDR(ht, COPY(HT_GET_DATA_ADDR(ht), HT_USED_SIZE(ht)));
		for (idx = 0; idx < ht->nNumUsed; idx++) {
			Bucket *p = ht->arData + idx;
			if (Z_TYPE(p->val) == IS_UNDEF) continue;

			if (ht->nInternalPointer == HT_INVALID_IDX) {
				ht->nInternalPointer = idx;
			}

			if (p->key) {
				p->key = apc_persist_copy_zstr_no_add(ctxt, p->key);
				p->key = TO_OFF(p->key);
				ht->u.flags &= ~HASH_FLAG_STATIC_KEYS;
			} else if ((zend_long) p->h >= (zend_long) ht->nNextFreeElement) {
				ht->nNextFreeElement = p->h + 1;
			}

			apc_persist_copy_zval(ctxt, &p->val);
		}

		ht->arData = TO_OFF(ht->arData);
	}

	return ht;
}

static void apc_persist_copy_serialize(
		apc_persist_context_t *ctxt, zval *zv) {
	zend_string *str;
	zend_uchar orig_type = Z_TYPE_P(zv);
	ZEND_ASSERT(orig_type == IS_ARRAY || orig_type == IS_OBJECT);

	ZEND_ASSERT(!ctxt->memoization_needed);
	ZEND_ASSERT(ctxt->serialized_str);
	str = apc_persist_copy_cstr(ctxt,
		(char *) ctxt->serialized_str, ctxt->serialized_str_len, 0);

	/* Store as PTR type to distinguish from other strings */
	ZVAL_PTR(zv, str);
}

static void apc_persist_copy_zval_impl(apc_persist_context_t *ctxt, zval *zv) {
	void *ptr;

	if (ctxt->use_serialization) {
		apc_persist_copy_serialize(ctxt, zv);
		return;
	}

	ptr = apc_persist_get_already_allocated(ctxt, Z_COUNTED_P(zv));
	switch (Z_TYPE_P(zv)) {
		case IS_STRING:
			if (!ptr) ptr = apc_persist_copy_zstr(ctxt, Z_STR_P(zv));
			ZVAL_STR(zv, ptr);
			return;
		case IS_ARRAY:
			if (!ptr) ptr = apc_persist_copy_ht(ctxt, Z_ARRVAL_P(zv));
			ZVAL_ARR(zv, ptr);
			return;
		case IS_REFERENCE:
			if (!ptr) ptr = apc_persist_copy_ref(ctxt, Z_REF_P(zv));
			ZVAL_REF(zv, ptr);
			return;
		EMPTY_SWITCH_DEFAULT_CASE()
	}
}

static apc_cache_entry_t *apc_persist_create_entry(
		apc_persist_context_t *ctxt, zend_string *key, const zval *zv)
{
	/* Get memory for the entry (incl. key) */
	apc_cache_entry_t *entry = ALLOC(APC_ENTRY_SIZE(ZSTR_LEN(key)));

	/* Deep copy of the key */
	GC_SET_REFCOUNT(&entry->key, 1);
	GC_SET_PERSISTENT_TYPE(&entry->key, IS_STRING);
	ZSTR_LEN(&entry->key) = ZSTR_LEN(key);
	memcpy(ZSTR_VAL(&entry->key), ZSTR_VAL(key), ZSTR_LEN(key));
	ZSTR_VAL(&entry->key)[ZSTR_LEN(key)] = '\0';
	ZSTR_H(&entry->key) = zend_string_hash_val(key);

	/* Deep copy of the value */
	ZVAL_COPY_VALUE(&entry->val, zv);
	apc_persist_copy_zval(ctxt, &entry->val);

	return entry;
}

apc_cache_entry_t *apc_persist(
		apc_sma_t *sma, apc_serializer_t *serializer, zend_string *key, const zval *val) {
	apc_persist_context_t ctxt;
	apc_cache_entry_t *entry;

	apc_persist_init_context(&ctxt, serializer);

	/* The top-level value should never be a reference */
	ZEND_ASSERT(Z_TYPE_P(val) != IS_REFERENCE);

	/* If we're serializing an array using the default serializer, we will have
	 * to keep track of potentially repeated refcounted structures. */
	if (!serializer && Z_TYPE_P(val) == IS_ARRAY) {
		ctxt.memoization_needed = 1;
		zend_hash_init(&ctxt.already_counted, 0, NULL, NULL, 0);
		zend_hash_init(&ctxt.already_allocated, 0, NULL, NULL, 0);
	}

	/* Objects are always serialized, and arrays when a serializer is set.
	 * Other cases are detected during apc_persist_calc(). */
	if (Z_TYPE_P(val) == IS_OBJECT
			|| (serializer && Z_TYPE_P(val) == IS_ARRAY)) {
		ctxt.use_serialization = 1;
	}

	if (!apc_persist_calc(&ctxt, key, val)) {
		if (!ctxt.use_serialization) {
			apc_persist_destroy_context(&ctxt);
			return NULL;
		}

		/* Try again with serialization */
		apc_persist_destroy_context(&ctxt);
		apc_persist_init_context(&ctxt, serializer);
		ctxt.use_serialization = 1;
		if (!apc_persist_calc(&ctxt, key, val)) {
			apc_persist_destroy_context(&ctxt);
			return NULL;
		}
	}

	ctxt.alloc = ctxt.alloc_cur = apc_sma_malloc(sma, ctxt.size);
	if (!ctxt.alloc) {
		apc_persist_destroy_context(&ctxt);
		return NULL;
	}

	entry = apc_persist_create_entry(&ctxt, key, val);
	ZEND_ASSERT(ctxt.alloc_cur == ctxt.alloc + ctxt.size);

	entry->mem_size = ctxt.size;

	apc_persist_destroy_context(&ctxt);
	return entry;
}

/*
 * UNPERSIST: Copy from SHM to request memory.
 */

typedef struct _apc_unpersist_context_t {
	/* Whether we need to memoize already copied refcounteds. */
	zend_bool memoization_needed;
	/* HashTable storing already copied refcounteds. */
	HashTable already_copied;
	/* Address (process local) of entry in shm / Whole SMA allocation */
	char *alloc;
} apc_unpersist_context_t;

/* TO_PTR() does the opposite of TO_OFF() and converts an offset stored in an entry (in shm)
 * into a (process local) pointer, which can then be used to access an element of that entry.
 * It expects the presence of a variable ctxt that points to an apc_unpersist_context_t. */
#define TO_PTR(off) (apc_unpersist_compute_pointer(off, ctxt))

static void apc_unpersist_zval_impl(apc_unpersist_context_t *ctxt, zval *zv);

static inline void *apc_unpersist_compute_pointer(void *off, apc_unpersist_context_t *ctxt) {
	/* The offset must be smaller than the size of the entry (in shm) to be unpersisted */
	assert((uintptr_t)off < (uintptr_t)((apc_cache_entry_t *)ctxt->alloc)->mem_size);

	return (void *)((uintptr_t)ctxt->alloc + (uintptr_t)off);
}

static inline void apc_unpersist_zval(apc_unpersist_context_t *ctxt, zval *zv) {
	/* No data apart from the zval itself */
	if (Z_TYPE_P(zv) < IS_STRING) {
		return;
	}

	Z_PTR_P(zv) = TO_PTR(Z_PTR_P(zv));
	apc_unpersist_zval_impl(ctxt, zv);
}

static zend_bool apc_unpersist_serialized(
		apc_unpersist_context_t *ctxt, zval *dst, zend_string *str, apc_serializer_t *serializer) {
	apc_unserialize_t unserialize = APC_UNSERIALIZER_NAME(php);
	void *config = NULL;

	if (serializer) {
		unserialize = serializer->unserialize;
		config = serializer->config;
	}

	str = TO_PTR(str);
	if (unserialize(dst, (unsigned char *) ZSTR_VAL(str), ZSTR_LEN(str), config)) {
		return 1;
	}

	ZVAL_NULL(dst);
	return 0;
}

static inline void *apc_unpersist_get_already_copied(apc_unpersist_context_t *ctxt, void *ptr) {
	if (ctxt->memoization_needed) {
		return zend_hash_index_find_ptr(&ctxt->already_copied, apc_shr3((zend_ulong)(uintptr_t)ptr));
	}
	return NULL;
}

static inline void apc_unpersist_add_already_copied(
		apc_unpersist_context_t *ctxt, const void *old_ptr, void *new_ptr) {
	if (ctxt->memoization_needed) {
		zend_hash_index_add_new_ptr(&ctxt->already_copied, apc_shr3((zend_ulong)(uintptr_t)old_ptr), new_ptr);
	}
}

static zend_string *apc_unpersist_zstr(apc_unpersist_context_t *ctxt, const zend_string *orig_str) {
	zend_string *str = zend_string_init(ZSTR_VAL(orig_str), ZSTR_LEN(orig_str), 0);
	ZSTR_H(str) = ZSTR_H(orig_str);
	apc_unpersist_add_already_copied(ctxt, orig_str, str);
	return str;
}

static zend_reference *apc_unpersist_ref(
		apc_unpersist_context_t *ctxt, const zend_reference *orig_ref) {
	zend_reference *ref = emalloc(sizeof(zend_reference));
	apc_unpersist_add_already_copied(ctxt, orig_ref, ref);

	GC_SET_REFCOUNT(ref, 1);
	GC_TYPE_INFO(ref) = GC_REFERENCE;
#if PHP_VERSION_ID >= 70400
	ref->sources.ptr = NULL;
#endif

	ZVAL_COPY_VALUE(&ref->val, &orig_ref->val);
	apc_unpersist_zval(ctxt, &ref->val);
	return ref;
}

/* Compute the size of the HashTable data to create when unpersisting. */
static zend_always_inline size_t apc_compute_ht_data_size(const HashTable *ht) {
#if PHP_VERSION_ID >= 80200
	if (HT_IS_PACKED(ht)) {
		return HT_PACKED_SIZE(ht);
	}
#endif
	return HT_SIZE(ht);
}

static zend_array *apc_unpersist_ht(
		apc_unpersist_context_t *ctxt, const HashTable *orig_ht) {
	HashTable *ht = emalloc(sizeof(HashTable));

	apc_unpersist_add_already_copied(ctxt, orig_ht, ht);
	memcpy(ht, orig_ht, sizeof(HashTable));
	GC_TYPE_INFO(ht) = GC_ARRAY;
#if PHP_VERSION_ID >= 70300
	/* Caller used ZVAL_EMPTY_ARRAY and set different zval flags instead */
	ZEND_ASSERT(ht->nNumOfElements > 0 && ht->nNumUsed > 0);
#else
	if (ht->nNumUsed == 0) {
		HT_SET_DATA_ADDR(ht, &uninitialized_bucket);
		return ht;
	}
#endif

	HT_SET_DATA_ADDR(ht, emalloc(apc_compute_ht_data_size(ht)));
	memcpy(HT_GET_DATA_ADDR(ht), TO_PTR(HT_GET_DATA_ADDR(orig_ht)), HT_HASH_SIZE(ht->nTableMask));

#if PHP_VERSION_ID >= 80200
	if (HT_IS_PACKED(ht)) {
		zval *p = ht->arPacked, *q = TO_PTR(orig_ht->arPacked), *p_end = p + ht->nNumUsed;
		for (; p < p_end; p++, q++) {
			*p = *q;
			apc_unpersist_zval(ctxt, p);
		}
	} else
#endif
	if (ht->u.flags & HASH_FLAG_STATIC_KEYS) {
		Bucket *p = ht->arData, *q = TO_PTR(orig_ht->arData), *p_end = p + ht->nNumUsed;
		for (; p < p_end; p++, q++) {
			/* No need to check for UNDEF, as unpersist_zval can be safely called on UNDEF */
			*p = *q;
			apc_unpersist_zval(ctxt, &p->val);
		}
	} else {
		Bucket *p = ht->arData, *q = TO_PTR(orig_ht->arData), *p_end = p + ht->nNumUsed;
		for (; p < p_end; p++, q++) {
			if (Z_TYPE(q->val) == IS_UNDEF) {
				ZVAL_UNDEF(&p->val);
				continue;
			}

			p->val = q->val;
			p->h = q->h;
			if (q->key) {
				p->key = zend_string_dup(TO_PTR(q->key), 0);
			} else {
				p->key = NULL;
			}
			apc_unpersist_zval(ctxt, &p->val);
		}
	}

	return ht;
}

static void apc_unpersist_zval_impl(apc_unpersist_context_t *ctxt, zval *zv) {
	void *ptr = apc_unpersist_get_already_copied(ctxt, Z_COUNTED_P(zv));
	if (ptr) {
		Z_COUNTED_P(zv) = ptr;
		Z_ADDREF_P(zv);
		return;
	}

	switch (Z_TYPE_P(zv)) {
		case IS_STRING:
			Z_STR_P(zv) = apc_unpersist_zstr(ctxt, Z_STR_P(zv));
			return;
		case IS_REFERENCE:
			Z_REF_P(zv) = apc_unpersist_ref(ctxt, Z_REF_P(zv));
			return;
		case IS_ARRAY:
#if PHP_VERSION_ID >= 70300
			if (Z_ARR_P(zv) == (zend_array *)ctxt->alloc) {
				/* If the zval points to the entry's starting address, we use the zend_empty_array optimization. */
				ZVAL_EMPTY_ARRAY(zv); /* #323 */
				return;
			}
#endif
			Z_ARR_P(zv) = apc_unpersist_ht(ctxt, Z_ARR_P(zv));
			return;
		default:
			ZEND_ASSERT(0);
			return;
	}
}

zend_bool apc_unpersist(zval *dst, const apc_cache_entry_t *entry, apc_serializer_t *serializer) {
	apc_unpersist_context_t ctxt;

	/* Needed to convert offsets back to pointers */
	ctxt.alloc = (char *)entry;

	if (Z_TYPE(entry->val) == IS_PTR) {
		return apc_unpersist_serialized(&ctxt, dst, Z_PTR(entry->val), serializer);
	}

	ctxt.memoization_needed = 0;
	ZEND_ASSERT(Z_TYPE(entry->val) != IS_REFERENCE);
	if (Z_TYPE(entry->val) == IS_ARRAY) {
		ctxt.memoization_needed = 1;
		zend_hash_init(&ctxt.already_copied, 0, NULL, NULL, 0);
	}

	ZVAL_COPY_VALUE(dst, &entry->val);
	apc_unpersist_zval(&ctxt, dst);

	if (ctxt.memoization_needed) {
		zend_hash_destroy(&ctxt.already_copied);
	}
	return 1;
}
