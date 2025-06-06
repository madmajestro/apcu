/*
  +----------------------------------------------------------------------+
  | APC                                                                  |
  +----------------------------------------------------------------------+
  | Copyright (c) 2006-2011 The PHP Group                                |
  +----------------------------------------------------------------------+
  | This source file is subject to version 3.01 of the PHP license,      |
  | that is bundled with this package in the file LICENSE, and is        |
  | available through the world-wide-web at the following url:           |
  | http://www.php.net/license/3_01.txt                                  |
  | If you did not receive a copy of the PHP license and are unable to   |
  | obtain it through the world-wide-web, please send a note to          |
  | license@php.net so we can mail you a copy immediately.               |
  +----------------------------------------------------------------------+
  | Authors: Daniel Cowgill <dcowgill@communityconnect.com>              |
  |          Rasmus Lerdorf <rasmus@php.net>                             |
  +----------------------------------------------------------------------+

   This software was contributed to PHP by Community Connect Inc. in 2002
   and revised in 2005 by Yahoo! Inc. to add support for PHP 5.1.
   Future revisions and derivatives of this source code must acknowledge
   Community Connect Inc. as the original contributor of this module by
   leaving this note intact in the source code.

   All other licensing and usage conditions are those of the PHP Group.

 */

#ifdef HAVE_CONFIG_H
# include "config.h"
#endif

#include "apc_cache.h"
#include "apc_iterator.h"
#include "apc_sma.h"
#include "apc_lock.h"
#include "apc_mutex.h"
#include "apc_strings.h"
#include "apc_time.h"
#include "php_globals.h"
#include "php_ini.h"
#include "ext/standard/info.h"
#include "ext/standard/file.h"
#include "ext/standard/flock_compat.h"
#include "ext/standard/md5.h"
#include "ext/standard/php_var.h"
#if PHP_VERSION_ID >= 80000
# include "php_apc_arginfo.h"
#else
# include "php_apc_legacy_arginfo.h"
#endif
#include "php74_shim.h"

#ifdef HAVE_SYS_FILE_H
#include <sys/file.h>
#endif

#include "SAPI.h"
#include "php_apc.h"

#ifdef HAVE_SIGACTION
#include "apc_signal.h"
#endif

/* {{{ ZEND_DECLARE_MODULE_GLOBALS(apcu) */
ZEND_DECLARE_MODULE_GLOBALS(apcu)

/* True globals */
apc_cache_t* apc_user_cache = NULL;

/* External APC SMA */
apc_sma_t apc_sma;

#define X(str) zend_string *apc_str_ ## str;
	APC_STRINGS
#undef X

/* Global init functions */
static void php_apc_init_globals(zend_apcu_globals* apcu_globals)
{
	apcu_globals->initialized = 0;
	apcu_globals->slam_defense = 0;
	apcu_globals->smart = 0;
	apcu_globals->preload_path = NULL;
	apcu_globals->coredump_unmap = 0;
	apcu_globals->use_request_time = 0;
	apcu_globals->serializer_name = NULL;
	apcu_globals->entry_level = 0;
}
/* }}} */

/* {{{ PHP_INI */

static PHP_INI_MH(OnUpdateShmSize) /* {{{ */
{
#if PHP_VERSION_ID >= 80200
	zend_long s = zend_ini_parse_quantity_warn(new_value, entry->name);
#else
	zend_long s = zend_atol(new_value->val, new_value->len);
#endif

	if (s <= 0) {
		return FAILURE;
	}

	if (s < Z_L(1048576)) {
		/* if it's less than 1Mb, they are probably using the old syntax */
		php_error_docref(
			NULL, E_WARNING, "apc.shm_size now uses M/G suffixes, please update your ini files");
		s = s * Z_L(1048576);
	}

	APCG(shm_size) = s;

	return SUCCESS;
}
/* }}} */

#if defined(APC_MMAP)
static PHP_INI_MH(OnUpdateMmapHugepageSize) /* {{{ */
{
	zend_long s;

#if PHP_VERSION_ID >= 80200
	s = zend_ini_parse_quantity_warn(new_value, entry->name);
#else
	s = zend_atol(new_value->val, new_value->len);
#endif

	if (s < 0) {
		php_error_docref(NULL, E_CORE_ERROR, "apc.mmap_hugepage_size must be a positive integer");
		return FAILURE;
	}

	if (s & (s - 1)) {
		php_error_docref(NULL, E_CORE_ERROR, "apc.mmap_hugepage_size must be a power of 2");
		return FAILURE;
	}

	APCG(mmap_hugepage_size) = s;
	return SUCCESS;
}
/* }}} */
#endif

PHP_INI_BEGIN()
STD_PHP_INI_BOOLEAN("apc.enabled",      "1",    PHP_INI_SYSTEM, OnUpdateBool,              enabled,          zend_apcu_globals, apcu_globals)
STD_PHP_INI_ENTRY("apc.shm_size",       "32M",  PHP_INI_SYSTEM, OnUpdateShmSize,           shm_size,         zend_apcu_globals, apcu_globals)
STD_PHP_INI_ENTRY("apc.entries_hint",   "0",    PHP_INI_SYSTEM, OnUpdateLong,              entries_hint,     zend_apcu_globals, apcu_globals)
STD_PHP_INI_ENTRY("apc.gc_ttl",         "3600", PHP_INI_SYSTEM, OnUpdateLong,              gc_ttl,           zend_apcu_globals, apcu_globals)
STD_PHP_INI_ENTRY("apc.ttl",            "0",    PHP_INI_SYSTEM, OnUpdateLong,              ttl,              zend_apcu_globals, apcu_globals)
STD_PHP_INI_ENTRY("apc.smart",          "0",    PHP_INI_SYSTEM, OnUpdateLong,              smart,            zend_apcu_globals, apcu_globals)
#ifdef APC_MMAP
STD_PHP_INI_ENTRY("apc.mmap_file_mask", NULL,   PHP_INI_SYSTEM, OnUpdateString,            mmap_file_mask,    zend_apcu_globals, apcu_globals)
STD_PHP_INI_ENTRY("apc.mmap_hugepage_size", "0", PHP_INI_SYSTEM, OnUpdateMmapHugepageSize, mmap_hugepage_size, zend_apcu_globals, apcu_globals)
#endif
STD_PHP_INI_BOOLEAN("apc.enable_cli",   "0",    PHP_INI_SYSTEM, OnUpdateBool,              enable_cli,       zend_apcu_globals, apcu_globals)
STD_PHP_INI_BOOLEAN("apc.slam_defense", "0",    PHP_INI_SYSTEM, OnUpdateBool,              slam_defense,     zend_apcu_globals, apcu_globals)
STD_PHP_INI_ENTRY("apc.preload_path", (char*)NULL,              PHP_INI_SYSTEM, OnUpdateString,       preload_path,  zend_apcu_globals, apcu_globals)
STD_PHP_INI_BOOLEAN("apc.coredump_unmap", "0", PHP_INI_SYSTEM, OnUpdateBool, coredump_unmap, zend_apcu_globals, apcu_globals)
STD_PHP_INI_BOOLEAN("apc.use_request_time", "0", PHP_INI_ALL, OnUpdateBool, use_request_time,  zend_apcu_globals, apcu_globals)
STD_PHP_INI_ENTRY("apc.serializer", "php", PHP_INI_SYSTEM, OnUpdateStringUnempty, serializer_name, zend_apcu_globals, apcu_globals)
PHP_INI_END()

/* }}} */

zend_bool apc_is_enabled(void)
{
	return APCG(enabled);
}

/* {{{ PHP_MINFO_FUNCTION(apcu) */
static PHP_MINFO_FUNCTION(apcu)
{
	php_info_print_table_start();
	php_info_print_table_row(2, "APCu Support", APCG(enabled) ? "Enabled" : "Disabled");
	php_info_print_table_row(2, "Version", PHP_APCU_VERSION);
#ifdef APC_DEBUG
	php_info_print_table_row(2, "APCu Debugging", "Enabled");
#else
	php_info_print_table_row(2, "APCu Debugging", "Disabled");
#endif
#ifdef APC_MMAP
	php_info_print_table_row(2, "MMAP Support", "Enabled");
	php_info_print_table_row(2, "MMAP File Mask", APCG(mmap_file_mask));
#else
	php_info_print_table_row(2, "MMAP Support", "Disabled");
#endif

	if (APCG(enabled)) {
		apc_serializer_t *serializer = NULL;
		smart_str names = {0,};
		int i;

		for( i = 0, serializer = apc_get_serializers();
					serializer->name != NULL;
					serializer++, i++) {
			if (i != 0) {
				smart_str_appends(&names, ", ");
			}
			smart_str_appends(&names, serializer->name);
		}

		if (names.s) {
			smart_str_0(&names);
			php_info_print_table_row(2, "Serialization Support", names.s->val);
			smart_str_free(&names);
		} else {
			php_info_print_table_row(2, "Serialization Support", "Broken");
		}
	} else {
		php_info_print_table_row(2, "Serialization Support", "Disabled");
	}

	php_info_print_table_row(2, "Build Date", __DATE__ " " __TIME__);
	php_info_print_table_end();
	DISPLAY_INI_ENTRIES();
}
/* }}} */

/* {{{ PHP_MINIT_FUNCTION(apcu) */
static PHP_MINIT_FUNCTION(apcu)
{
#if defined(ZTS) && defined(COMPILE_DL_APCU)
	ZEND_TSRMLS_CACHE_UPDATE();
#endif
	ZEND_INIT_MODULE_GLOBALS(apcu, php_apc_init_globals, NULL);

	REGISTER_INI_ENTRIES();

#define X(str) \
	apc_str_ ## str = zend_new_interned_string( \
		zend_string_init(#str, sizeof(#str) - 1, 1));
	APC_STRINGS
#undef X

	/* locks initialized regardless of settings */
	apc_lock_init();
	APC_MUTEX_INIT();

	/* Disable APC in cli mode unless overridden by apc.enable_cli */
	if (!APCG(enable_cli) && !strcmp(sapi_module.name, "cli")) {
		APCG(enabled) = 0;
	}

	/* only run initialization if APC is enabled */
	if (APCG(enabled)) {

		if (!APCG(initialized)) {
			char *mmap_file_mask = NULL;
			zend_long mmap_hugepage_size = 0;

#ifdef APC_MMAP
			mmap_file_mask = APCG(mmap_file_mask);
			mmap_hugepage_size = APCG(mmap_hugepage_size);
#endif

			/* ensure this runs only once */
			APCG(initialized) = 1;

			/* initialize shared memory allocator */
			apc_sma_init(
				&apc_sma, (void **) &apc_user_cache, (apc_sma_expunge_f) apc_cache_default_expunge,
				APCG(shm_size), APC_ENTRY_SIZE(0), mmap_file_mask, mmap_hugepage_size);

			REGISTER_LONG_CONSTANT(APC_SERIALIZER_CONSTANT, (zend_long)&_apc_register_serializer, CONST_PERSISTENT | CONST_CS);

			/* register default serializer */
			_apc_register_serializer(
				"php", APC_SERIALIZER_NAME(php), APC_UNSERIALIZER_NAME(php), NULL);

			/* test out the constant function pointer */
			assert(apc_get_serializers()->name != NULL);

			/* create user cache */
			apc_user_cache = apc_cache_create(
				&apc_sma,
				apc_find_serializer(APCG(serializer_name)),
				APCG(entries_hint), APCG(gc_ttl), APCG(ttl), APCG(smart), APCG(slam_defense));

			/* preload data from path specified in configuration */
			if (APCG(preload_path)) {
				apc_cache_preload(
					apc_user_cache, APCG(preload_path));
			}
		}
	}

	/* initialize iterator object */
	apc_iterator_init(module_number);

	return SUCCESS;
}
/* }}} */

/* {{{ PHP_MSHUTDOWN_FUNCTION(apcu) */
static PHP_MSHUTDOWN_FUNCTION(apcu)
{
#define X(str) zend_string_release(apc_str_ ## str);
	APC_STRINGS
#undef X

	/* locks shutdown regardless of settings */
	apc_lock_cleanup();
	APC_MUTEX_CLEANUP();

	/* only shut down if APC is enabled */
	if (APCG(enabled)) {
		if (APCG(initialized)) {
			/* Detach cache and shared memory allocator from shared memory. */
			apc_cache_detach(apc_user_cache);
			apc_sma_detach(&apc_sma);

			APCG(initialized) = 0;
		}

#ifdef HAVE_SIGACTION
		apc_shutdown_signals();
#endif
	}

	apc_iterator_shutdown(module_number);

	UNREGISTER_INI_ENTRIES();
	return SUCCESS;
} /* }}} */

/* {{{ PHP_RINIT_FUNCTION(apcu) */
static PHP_RINIT_FUNCTION(apcu)
{
#if defined(ZTS) && defined(COMPILE_DL_APCU)
	ZEND_TSRMLS_CACHE_UPDATE();
#endif

	APCG(request_time) = 0;
	if (APCG(enabled)) {
		if (APCG(serializer_name)) {
			/* Avoid race conditions between MINIT of apc and serializer exts like igbinary */
			apc_cache_serializer(apc_user_cache, APCG(serializer_name));
		}

#ifdef HAVE_SIGACTION
		apc_set_signals();
#endif
	}
	return SUCCESS;
}
/* }}} */

/* {{{ proto void apcu_clear_cache() */
PHP_FUNCTION(apcu_clear_cache)
{
	if (zend_parse_parameters_none() == FAILURE) {
		return;
	}

	apc_cache_clear(apc_user_cache);
	RETURN_TRUE;
}
/* }}} */

/* {{{ proto array apcu_cache_info([bool limited]) */
PHP_FUNCTION(apcu_cache_info)
{
	zend_bool limited = 0;

	ZEND_PARSE_PARAMETERS_START(0,1)
		Z_PARAM_OPTIONAL
		Z_PARAM_BOOL(limited)
	ZEND_PARSE_PARAMETERS_END();

	if (!apc_cache_info(return_value, apc_user_cache, limited)) {
		php_error_docref(NULL, E_WARNING, "No APC info available.  Perhaps APC is not enabled? Check apc.enabled in your ini file");
		RETURN_FALSE;
	}
}
/* }}} */

/* {{{ proto array apcu_key_info(string key) */
PHP_FUNCTION(apcu_key_info)
{
	zend_string *key;

	ZEND_PARSE_PARAMETERS_START(1, 1)
		Z_PARAM_STR(key)
	ZEND_PARSE_PARAMETERS_END();

	apc_cache_stat(apc_user_cache, key, return_value);
} /* }}} */

/* {{{ proto array apcu_sma_info([bool limited]) */
PHP_FUNCTION(apcu_sma_info)
{
	zend_bool limited = 0;

	ZEND_PARSE_PARAMETERS_START(0, 1)
		Z_PARAM_OPTIONAL
		Z_PARAM_BOOL(limited)
	ZEND_PARSE_PARAMETERS_END();

	apc_sma_info_t *info = apc_sma_info(&apc_sma, limited);

	if (!info) {
		php_error_docref(NULL, E_WARNING, "No APC SMA info available.  Perhaps APC is disabled via apc.enabled?");
		RETURN_FALSE;
	}

	array_init(return_value);
	add_assoc_long(return_value, "num_seg", 1);
	add_assoc_double(return_value, "seg_size", (double)info->seg_size);
	add_assoc_double(return_value, "avail_mem", (double)apc_sma_get_avail_mem(&apc_sma));

	if (limited) {
		apc_sma_free_info(&apc_sma, info);
		return;
	}

	/* generate list of free blocks */
	apc_sma_link_t *p;
	zval list;
	array_init(&list);
	for (p = info->list; p != NULL; p = p->next) {
		zval link;

		array_init(&link);
		add_assoc_long(&link, "size", p->size);
		add_assoc_long(&link, "offset", p->offset);
		add_next_index_zval(&list, &link);
	}

	/* Since support for multiple shm segments has been dropped, the "block_lists" array
	 * only exists to ensure compatibility with existing PHP scripts. */
	zval block_lists;
	array_init(&block_lists);
	add_next_index_zval(&block_lists, &list);

	add_assoc_zval(return_value, "block_lists", &block_lists);
	apc_sma_free_info(&apc_sma, info);
}
/* }}} */

/* {{{ php_apc_update  */
zend_bool php_apc_update(
		zend_string *key, apc_cache_atomic_updater_t updater, void *data,
		zend_bool insert_if_not_found, time_t ttl)
{
	if (APCG(serializer_name)) {
		/* Avoid race conditions between MINIT of apc and serializer exts like igbinary */
		apc_cache_serializer(apc_user_cache, APCG(serializer_name));
	}

	return apc_cache_atomic_update_long(apc_user_cache, key, updater, data, insert_if_not_found, ttl);
}
/* }}} */

/* {{{ apc_store_helper(INTERNAL_FUNCTION_PARAMETERS, const zend_bool exclusive)
 */
static void apc_store_helper(INTERNAL_FUNCTION_PARAMETERS, const zend_bool exclusive)
{
	zval *key;
	zval *val = NULL;
	zend_long ttl = 0L;

	ZEND_PARSE_PARAMETERS_START(1, 3)
		Z_PARAM_ZVAL(key)
		Z_PARAM_OPTIONAL
		Z_PARAM_ZVAL(val)
		Z_PARAM_LONG(ttl)
	ZEND_PARSE_PARAMETERS_END();

	if (APCG(serializer_name)) {
		/* Avoid race conditions between MINIT of apc and serializer exts like igbinary */
		apc_cache_serializer(apc_user_cache, APCG(serializer_name));
	}

	/* TODO: Port to array|string for PHP 8? */
	if (Z_TYPE_P(key) == IS_ARRAY) {
		zval *hentry;
		zend_string *hkey;
		zend_ulong hkey_idx;
		HashTable* hash = Z_ARRVAL_P(key);

		/* We only insert keys that failed */
		zval fail_zv;
		ZVAL_LONG(&fail_zv, -1);
		array_init(return_value);

		ZEND_HASH_FOREACH_KEY_VAL(hash, hkey_idx, hkey, hentry) {
			ZVAL_DEREF(hentry);
			if (hkey) {
				zend_string_addref(hkey);
			} else {
				hkey = zend_long_to_str(hkey_idx);
			}
			if (!apc_cache_store(apc_user_cache, hkey, hentry, (uint32_t) ttl, exclusive)) {
				zend_symtable_add_new(Z_ARRVAL_P(return_value), hkey, &fail_zv);
			}
			zend_string_release(hkey);
		} ZEND_HASH_FOREACH_END();
		return;
	} else if (Z_TYPE_P(key) == IS_STRING) {
		if (!val) {
			/* nothing to store */
			RETURN_FALSE;
		}

		RETURN_BOOL(apc_cache_store(apc_user_cache, Z_STR_P(key), val, (uint32_t) ttl, exclusive));
	} else {
		apc_warning("apc_store expects key parameter to be a string or an array of key/value pairs.");
		RETURN_FALSE;
	}
}
/* }}} */

/* {{{ proto bool apcu_enabled(void)
	returns true when apcu is usable in the current environment */
PHP_FUNCTION(apcu_enabled) {
	if (zend_parse_parameters_none() == FAILURE) {
		return;
	}
	RETURN_BOOL(APCG(enabled));
}
/* }}} */

/* {{{ proto int apcu_store(mixed key, mixed var [, long ttl ])
 */
PHP_FUNCTION(apcu_store) {
	apc_store_helper(INTERNAL_FUNCTION_PARAM_PASSTHRU, 0);
}
/* }}} */

/* {{{ proto int apcu_add(mixed key, mixed var [, long ttl ])
 */
PHP_FUNCTION(apcu_add) {
	apc_store_helper(INTERNAL_FUNCTION_PARAM_PASSTHRU, 1);
}
/* }}} */

/* {{{ php_inc_updater */

struct php_inc_updater_args {
	zend_long step;
	zend_long rval;
};

static zend_bool php_inc_updater(apc_cache_t *cache, zend_long *entry, void *data) {
	struct php_inc_updater_args *args = (struct php_inc_updater_args *) data;
	args->rval = ATOMIC_ADD(*entry, args->step);
	return 1;
}

/* {{{ proto long apcu_inc(string key [, long step [, bool& success [, long ttl]]])
 */
PHP_FUNCTION(apcu_inc) {
	zend_string *key;
	struct php_inc_updater_args args;
	zend_long step = 1, ttl = 0;
	zval *success = NULL;

	ZEND_PARSE_PARAMETERS_START(1, 4)
		Z_PARAM_STR(key)
		Z_PARAM_OPTIONAL
		Z_PARAM_LONG(step)
		Z_PARAM_ZVAL(success)
		Z_PARAM_LONG(ttl)
	ZEND_PARSE_PARAMETERS_END();

	args.step = step;
	if (php_apc_update(key, php_inc_updater, &args, 1, ttl)) {
		if (success) {
			ZEND_TRY_ASSIGN_REF_TRUE(success);
		}
		RETURN_LONG(args.rval);
	}

	if (success) {
		ZEND_TRY_ASSIGN_REF_FALSE(success);
	}

	RETURN_FALSE;
}
/* }}} */

/* {{{ proto long apcu_dec(string key [, long step [, bool &success [, long ttl]]])
 */
PHP_FUNCTION(apcu_dec) {
	zend_string *key;
	struct php_inc_updater_args args;
	zend_long step = 1, ttl = 0;
	zval *success = NULL;

	ZEND_PARSE_PARAMETERS_START(1, 4)
		Z_PARAM_STR(key)
		Z_PARAM_OPTIONAL
		Z_PARAM_LONG(step)
		Z_PARAM_ZVAL(success)
		Z_PARAM_LONG(ttl)
	ZEND_PARSE_PARAMETERS_END();

	args.step = 0 - step;
	if (php_apc_update(key, php_inc_updater, &args, 1, ttl)) {
		if (success) {
			ZEND_TRY_ASSIGN_REF_TRUE(success);
		}

		RETURN_LONG(args.rval);
	}

	if (success) {
		ZEND_TRY_ASSIGN_REF_FALSE(success);
	}

	RETURN_FALSE;
}
/* }}} */

/* {{{ php_cas_updater */
static zend_bool php_cas_updater(apc_cache_t *cache, zend_long *entry, void *data) {
	zend_long *vals = (zend_long *) data;
	zend_long old = vals[0];
	zend_long new = vals[1];
	return ATOMIC_CAS(*entry, old, new);
}
/* }}} */

/* {{{ proto int apcu_cas(string key, int old, int new)
 */
PHP_FUNCTION(apcu_cas) {
	zend_string *key;
	zend_long vals[2];

	ZEND_PARSE_PARAMETERS_START(3, 3)
		Z_PARAM_STR(key)
		Z_PARAM_LONG(vals[0])
		Z_PARAM_LONG(vals[1])
	ZEND_PARSE_PARAMETERS_END();

	if (APCG(serializer_name)) {
		/* Avoid race conditions between MINIT of apc and serializer exts like igbinary */
		apc_cache_serializer(apc_user_cache, APCG(serializer_name));
	}

	RETURN_BOOL(apc_cache_atomic_update_long(apc_user_cache, key, php_cas_updater, &vals, 0, 0));
}
/* }}} */

/* {{{ proto mixed apcu_fetch(mixed key[, bool &success])
 */
PHP_FUNCTION(apcu_fetch) {
	zval *key;
	zval *success = NULL;
	time_t t;
	int result;

	ZEND_PARSE_PARAMETERS_START(1, 2)
		Z_PARAM_ZVAL(key)
		Z_PARAM_OPTIONAL
		Z_PARAM_ZVAL(success)
	ZEND_PARSE_PARAMETERS_END();

	t = apc_time();

	if (Z_TYPE_P(key) != IS_STRING && Z_TYPE_P(key) != IS_ARRAY) {
		convert_to_string(key);
	}

	/* TODO: Port to array|string for PHP 8? */
	if (Z_TYPE_P(key) == IS_STRING) {
		result = apc_cache_fetch(apc_user_cache, Z_STR_P(key), t, return_value);
	} else if (Z_TYPE_P(key) == IS_ARRAY) {
		zval *hentry;

		array_init(return_value);
		ZEND_HASH_FOREACH_VAL(Z_ARRVAL_P(key), hentry) {
			ZVAL_DEREF(hentry);
			if (Z_TYPE_P(hentry) == IS_STRING) {
				zval result_entry;
				ZVAL_UNDEF(&result_entry);

				if (apc_cache_fetch(apc_user_cache, Z_STR_P(hentry), t, &result_entry)) {
					zend_hash_update(Z_ARRVAL_P(return_value), Z_STR_P(hentry), &result_entry);
				}
			} else {
				apc_warning("apc_fetch() expects a string or array of strings.");
			}
		} ZEND_HASH_FOREACH_END();
		result = 1;
	} else {
		apc_warning("apc_fetch() expects a string or array of strings.");
		result = 0;
	}

	if (success) {
		ZEND_TRY_ASSIGN_REF_BOOL(success, result);
	}
	if (!result) {
		RETURN_FALSE;
	}
}
/* }}} */

/* {{{ proto mixed apcu_exists(mixed key)
 */
PHP_FUNCTION(apcu_exists) {
	zval *key;
	time_t t;

	ZEND_PARSE_PARAMETERS_START(1, 1)
		Z_PARAM_ZVAL(key)
	ZEND_PARSE_PARAMETERS_END();

	t = apc_time();

	if (Z_TYPE_P(key) != IS_STRING && Z_TYPE_P(key) != IS_ARRAY) {
		convert_to_string(key);
	}

	/* TODO: Port to array|string for PHP 8? */
	if (Z_TYPE_P(key) == IS_STRING) {
		RETURN_BOOL(apc_cache_exists(apc_user_cache, Z_STR_P(key), t));
	} else if (Z_TYPE_P(key) == IS_ARRAY) {
		zval *hentry;
		zval true_zv;
		ZVAL_TRUE(&true_zv);

		array_init(return_value);
		ZEND_HASH_FOREACH_VAL(Z_ARRVAL_P(key), hentry) {
			ZVAL_DEREF(hentry);
			if (Z_TYPE_P(hentry) == IS_STRING) {
				if (apc_cache_exists(apc_user_cache, Z_STR_P(hentry), t)) {
					  zend_hash_add_new(Z_ARRVAL_P(return_value), Z_STR_P(hentry), &true_zv);
				}
			} else {
				apc_warning(
					"apc_exists() expects a string or array of strings.");
			}
		} ZEND_HASH_FOREACH_END();
	} else {
		apc_warning("apc_exists() expects a string or array of strings.");
		RETURN_FALSE;
	}
}
/* }}} */

/* {{{ proto mixed apcu_delete(mixed keys)
 */
PHP_FUNCTION(apcu_delete) {
	zval *keys;

	ZEND_PARSE_PARAMETERS_START(1, 1)
		Z_PARAM_ZVAL(keys)
	ZEND_PARSE_PARAMETERS_END();

	if (Z_TYPE_P(keys) == IS_STRING) {
		RETURN_BOOL(apc_cache_delete(apc_user_cache, Z_STR_P(keys)));
	} else if (Z_TYPE_P(keys) == IS_ARRAY) {
		zval *hentry;

		array_init(return_value);
		ZEND_HASH_FOREACH_VAL(Z_ARRVAL_P(keys), hentry) {
			ZVAL_DEREF(hentry);
			if (Z_TYPE_P(hentry) != IS_STRING) {
				apc_warning("apc_delete() expects a string, array of strings, or APCIterator instance");
				add_next_index_zval(return_value, hentry);
				Z_TRY_ADDREF_P(hentry);
			} else if (apc_cache_delete(apc_user_cache, Z_STR_P(hentry)) != 1) {
				add_next_index_zval(return_value, hentry);
				Z_TRY_ADDREF_P(hentry);
			}
		} ZEND_HASH_FOREACH_END();
	} else if (Z_TYPE_P(keys) == IS_OBJECT) {
		RETURN_BOOL(apc_iterator_delete(keys) != 0);
	} else {
		apc_warning("apc_delete() expects a string, array of strings, or APCIterator instance");
		RETURN_FALSE;
	}
}

PHP_FUNCTION(apcu_entry) {
	zend_string *key;
	zend_fcall_info fci = empty_fcall_info;
	zend_fcall_info_cache fcc = empty_fcall_info_cache;
	zend_long ttl = 0L;
	zend_long now = apc_time();

	ZEND_PARSE_PARAMETERS_START(2, 3)
		Z_PARAM_STR(key)
		Z_PARAM_FUNC(fci, fcc)
		Z_PARAM_OPTIONAL
		Z_PARAM_LONG(ttl)
	ZEND_PARSE_PARAMETERS_END();

	apc_cache_entry(apc_user_cache, key, &fci, &fcc, ttl, now, return_value);
}
/* }}} */

#ifdef APC_DEBUG
/* This function is used to test TTL behavior without having to perform sleeps. */
PHP_FUNCTION(apcu_inc_request_time) {
	zend_long by = 1;

	ZEND_PARSE_PARAMETERS_START(0, 1)
		Z_PARAM_OPTIONAL
		Z_PARAM_LONG(by)
	ZEND_PARSE_PARAMETERS_END();

	if (!APCG(use_request_time)) {
		php_error_docref(NULL, E_WARNING,
			"Trying to increment request time while use_request_time is disabled");
		return;
	}

	/* Ensure APCG(request_time) is primed */
	(void) apc_time();

	APCG(request_time) += by;
}
#endif

/* {{{ module definition structure */

zend_module_entry apcu_module_entry = {
	STANDARD_MODULE_HEADER,
	PHP_APCU_EXTNAME,
	ext_functions,
	PHP_MINIT(apcu),
	PHP_MSHUTDOWN(apcu),
	PHP_RINIT(apcu),
	NULL,
	PHP_MINFO(apcu),
	PHP_APCU_VERSION,
	STANDARD_MODULE_PROPERTIES
};
/* }}} */

#ifdef COMPILE_DL_APCU
ZEND_GET_MODULE(apcu)
#ifdef ZTS
ZEND_TSRMLS_CACHE_DEFINE();
#endif
#endif
/* }}} */

/*
 * Local variables:
 * tab-width: 4
 * c-basic-offset: 4
 * End:
 * vim>600: noexpandtab sw=4 ts=4 sts=4 fdm=marker
 * vim<600: noexpandtab sw=4 ts=4 sts=4
 */
