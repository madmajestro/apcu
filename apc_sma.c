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

#include "apc_sma.h"
#include "apc.h"
#include "apc_globals.h"
#include "apc_mutex.h"
#include "apc_shm.h"
#include "apc_cache.h"

#include <limits.h>
#include "apc_mmap.h"

#ifdef APC_SMA_DEBUG
# ifdef HAVE_VALGRIND_MEMCHECK_H
#  include <valgrind/memcheck.h>
# endif
# define APC_SMA_CANARIES 1
#endif

#define SMA_BINS 32

typedef struct sma_header_t sma_header_t;
struct sma_header_t {
	apc_mutex_t sma_lock;   /* segment lock */
	size_t min_block_size;  /* expected minimum size of allocated blocks */
	size_t avail;           /* bytes available (not necessarily contiguous) */
	size_t max_bin_index;   /* max bin index used */
	size_t bins[SMA_BINS];  /* bins for free blocks of different sizes */
};

#define SMA_DEFAULT_SEGSIZE (30*1024*1024)

#define SMA_HDR(sma)  ((sma_header_t*)sma->shmaddr)
#define SMA_ADDR(sma) ((char *)sma->shmaddr)
#define SMA_LCK(sma)  ((SMA_HDR(sma))->sma_lock)

#define SMA_CREATE_LOCK  APC_CREATE_MUTEX
#define SMA_DESTROY_LOCK APC_DESTROY_MUTEX
#define SMA_LOCK(sma) APC_MUTEX_LOCK(&SMA_LCK(sma))
#define SMA_UNLOCK(sma) APC_MUTEX_UNLOCK(&SMA_LCK(sma))

typedef struct block_t block_t;
struct block_t {
	size_t fnext;      /* offset in segment of next free block (MUST BE THE 1st FIELD OF THE STRUCT!) */
	size_t fprev;      /* offset in segment of prev free block */
	size_t size;       /* size of this block */
	size_t prev_size;  /* size of sequentially previous block, 0 if prev is allocated */
#ifdef APC_SMA_CANARIES
	size_t canary;     /* canary to check for memory overwrites */
#endif
};

/* The macros BLOCKAT and OFFSET are used for convenience throughout this
 * module. Both assume the presence of a variable smaheader that points to the
 * beginning of the shared memory segment. */
#define BLOCKAT(offset) ((block_t*)((char *)smaheader + offset))
#define OFFSET(block) ((size_t)(((char*)block) - (char*)smaheader))

/* macros for getting the next or previous sequential block */
#define NEXT_SBLOCK(block) ((block_t*)((char*)block + block->size))
#define PREV_SBLOCK(block) ((block_t*)((char*)block - block->prev_size))

/* Canary macros for setting, checking and resetting memory canaries */
#ifdef APC_SMA_CANARIES
	#define SET_CANARY(v) (v)->canary = 0x42424242
	#define CHECK_CANARY(v) assert((v)->canary == 0x42424242)
	#define RESET_CANARY(v) (v)->canary = -42
#else
	#define SET_CANARY(v)
	#define CHECK_CANARY(v)
	#define RESET_CANARY(v)
#endif

#define MINBLOCKSIZE (ALIGNWORD(1) + ALIGNWORD(sizeof(block_t)))

static inline void link_block(sma_header_t *smaheader, size_t *bin, block_t *cur) {
	cur->fnext = *bin;
	cur->fprev = OFFSET(bin);
	*bin = OFFSET(cur);

	if (cur->fnext) {
		BLOCKAT(cur->fnext)->fprev = *bin;
	}
}

static inline void unlink_block(sma_header_t *smaheader, block_t *cur) {
	BLOCKAT(cur->fprev)->fnext = cur->fnext;

	if (cur->fnext) {
		BLOCKAT(cur->fnext)->fprev = cur->fprev;
	}
}

static inline size_t bin_calc_index(sma_header_t *smaheader, size_t realsize) {

	if (realsize <= smaheader->min_block_size) {
		return 0;
	}

	size_t bin = 0;
	realsize = (realsize - smaheader->min_block_size) / ZEND_MM_ALIGNMENT;

	while (realsize >>= 1) {
		bin++;
	}

	if (bin > smaheader->max_bin_index) {
		bin = smaheader->max_bin_index;
	}

	return bin;
}

static inline void bin_store(sma_header_t *smaheader, block_t *cur) {
	size_t bin = bin_calc_index(smaheader, cur->size);

	link_block(smaheader, &smaheader->bins[bin], cur);
}

static inline block_t *bin_find_block(sma_header_t *smaheader, size_t realsize) {
	block_t *cur = NULL;
	size_t i;

	/* First, ensure that at least realsize free bytes are available, even if they are not contiguous. */
	if (smaheader->avail < realsize) {
		return NULL;
	}

	/* Calculate the bin index for the requested size */
	size_t bin = bin_calc_index(smaheader, realsize);

	/* Step 1: Check the first block in the selected bin */
	if (smaheader->bins[bin]) {
		cur = BLOCKAT(smaheader->bins[bin]);

		/* In the calculated bin, we need to check the size of the blocks */
		if (cur->size >= realsize) {
			return cur;
		}
	}

	/* Calculate the maximum bin index up to which we check in forward direction */
	size_t max_bin = bin + 1 > smaheader->max_bin_index ? smaheader->max_bin_index : bin + 1;

	/* Step 2: Check bins in forward direction */
	for (i = bin + 1; i <= max_bin; i++) {
		if (smaheader->bins[i]) {
			return BLOCKAT(smaheader->bins[i]);
		}
	}

	/* Step 3: Check bins in backward direction */
	for (i = smaheader->max_bin_index; i > max_bin; i--) {
		if (smaheader->bins[i]) {
			return BLOCKAT(smaheader->bins[i]);
		}
	}

	/* if no block could be found in upper bins, we check additional blocks of the calculated bin */
	if (cur) {
		/* For performance reasons, we do not check all blocks in the calculated bin.
		 * If all upper bins are empty and the first x blocks of the calculated bin are too small,
		 * it makes sense to abort so that the default expunge operation is executed to get larger blocks. */
		for (i = 1; i < 10 && cur->fnext; i++) {
			cur = BLOCKAT(cur->fnext);

			/* In the calculated bin, we need to check the size of the blocks */
			if (cur->size >= realsize) {
				return cur;
			}
		}
	}

	return NULL;
}

/* sma_allocate: tries to allocate at least size bytes of shared memory */
static APC_HOTSPOT void *sma_allocate(sma_header_t *smaheader, size_t size)
{
	block_t* cur;           /* working block in list */
	size_t realsize;        /* actual size of block needed, including block header */

	realsize = ALIGNWORD(size + ALIGNWORD(sizeof(block_t)));

	cur = bin_find_block(smaheader, realsize);
	if (!cur) {
		/* No suitable block found */
		return NULL;
	}

	/* remove cur from bin */
	unlink_block(smaheader, cur);

	if (cur->size >= realsize && cur->size < (realsize + smaheader->min_block_size)) {
		/* cur is big enough for realsize, but too small to split */
		NEXT_SBLOCK(cur)->prev_size = 0;  /* block is alloc'd */
	} else {
		/* cur is too big; split it into two smaller blocks */
		block_t* nxt;      /* the new block (chopped part of cur) */
		size_t oldsize;    /* size of cur before split */

		oldsize = cur->size;
		cur->size = realsize;
		nxt = NEXT_SBLOCK(cur);
		nxt->prev_size = 0;                       /* block is alloc'd */
		nxt->size = oldsize - realsize;           /* and fix the size */
		NEXT_SBLOCK(nxt)->prev_size = nxt->size;  /* adjust size */
		SET_CANARY(nxt);

		/* put nxt in the appropriate bin */
		bin_store(smaheader, nxt);
	}

	/* store used space to be able to reclaim unused space during defragmentation */
	cur->fnext = realsize;

	/* mark cur as allocated */
	cur->fprev = 0;

	/* update the segment header */
	smaheader->avail -= cur->size;

	SET_CANARY(cur);

	return (char *)(cur) + ALIGNWORD(sizeof(block_t));
}

/* sma_deallocate: deallocates the block at the given offset */
static APC_HOTSPOT void sma_deallocate(sma_header_t *smaheader, size_t offset)
{
	block_t* cur;       /* the new block to insert */
	block_t* prv;       /* the block before cur */
	block_t* nxt;       /* the block after cur */

	assert(offset >= ALIGNWORD(sizeof(block_t)));
	offset -= ALIGNWORD(sizeof(block_t));

	/* find position of new block in free list */
	cur = BLOCKAT(offset);

	/* update the segment header */
	smaheader->avail += cur->size;

	if (cur->prev_size != 0) {
		/* remove prv from bin */
		prv = PREV_SBLOCK(cur);
		unlink_block(smaheader, prv);

		/* cur and prv share an edge, combine them */
		prv->size += cur->size;

		RESET_CANARY(cur);
		cur = prv;
	}

	nxt = NEXT_SBLOCK(cur);
	if (nxt->fprev != 0) {
		assert(NEXT_SBLOCK(NEXT_SBLOCK(cur))->prev_size == nxt->size);
		/* remove nxt from bin */
		unlink_block(smaheader, nxt);

		/* cur and nxt shared an edge, combine them */
		cur->size += nxt->size;

		CHECK_CANARY(nxt);
		RESET_CANARY(nxt);
	}

	/* mark in the next block that the previous block is free */
	NEXT_SBLOCK(cur)->prev_size = cur->size;

	/* put free block in the appropriate bin */
	bin_store(smaheader, cur);
}

PHP_APCU_API void apc_sma_init(apc_sma_t* sma, void** data, apc_sma_expunge_f expunge, size_t size, size_t min_alloc_size, char *mask, zend_long hugepage_size) {
	if (sma->initialized) {
		return;
	}

	sma->initialized = 1;
	sma->expunge = expunge;
	sma->data = data;
	sma->size = ALIGNWORD(size > 0 ? size : SMA_DEFAULT_SEGSIZE);

#ifdef APC_MMAP
	sma->shmaddr = apc_mmap(mask, sma->size, hugepage_size);
#else
	sma->shmaddr = apc_shm_attach(sma->size);
#endif

	sma_header_t *smaheader = sma->shmaddr;
	SMA_CREATE_LOCK(&smaheader->sma_lock);
	smaheader->min_block_size = min_alloc_size > 0 ? ALIGNWORD(min_alloc_size + ALIGNWORD(sizeof(block_t))) : MINBLOCKSIZE;
	smaheader->avail = sma->size - ALIGNWORD(sizeof(sma_header_t)) - ALIGNWORD(sizeof(block_t));

	block_t *empty = BLOCKAT(ALIGNWORD(sizeof(sma_header_t)));
	empty->size = smaheader->avail;
	empty->fnext = 0;
	empty->fprev = 0;
	empty->prev_size = 0;
	SET_CANARY(empty);

	block_t *last = BLOCKAT(OFFSET(empty) + empty->size);
	last->size = 0;
	last->fnext = 0;
	last->fprev =  0;
	last->prev_size = empty->size;
	SET_CANARY(last);

	memset(smaheader->bins, 0, sizeof(size_t) * SMA_BINS);
	smaheader->max_bin_index = SMA_BINS - 1;
	smaheader->max_bin_index = bin_calc_index(smaheader, empty->size);
	bin_store(smaheader, empty);
}

PHP_APCU_API void apc_sma_detach(apc_sma_t* sma) {
	/* Important: This function should not clean up anything that's in shared memory,
	 * only detach our process-local use of it. In particular locks cannot be destroyed
	 * here. */

	assert(sma->initialized);
	sma->initialized = 0;

#ifdef APC_MMAP
	apc_unmap(sma->shmaddr, sma->size);
#else
	apc_shm_detach(sma->shmaddr);
#endif
}

PHP_APCU_API void* apc_sma_malloc(apc_sma_t* sma, size_t n, apc_sma_malloc_init_f init_callback) {
	zend_bool nuked = 0;

restart:
	assert(sma->initialized);

	if (!SMA_LOCK(sma)) {
		return NULL;
	}

	void *p = sma_allocate(SMA_HDR(sma), n);

	if (p) {
		if (init_callback) {
			/* Perform initializations that must be done before releasing the lock */
			init_callback(p);
		}

		SMA_UNLOCK(sma);
#ifdef VALGRIND_MALLOCLIKE_BLOCK
		VALGRIND_MALLOCLIKE_BLOCK(p, n, 0, 0);
#endif
		return p;
	}

	SMA_UNLOCK(sma);

	/* Expunge cache in hope of freeing up memory, but only once */
	if (!nuked) {
		/* nuke is not set if expunge() was skipped internally to get another try */
		nuked = sma->expunge(*sma->data, n);
		goto restart;
	}

	return NULL;
}

PHP_APCU_API void apc_sma_free(apc_sma_t* sma, void* p) {
	size_t offset;

	if (p == NULL) {
		return;
	}

	assert(sma->initialized);

	offset = (size_t)((char *)p - SMA_ADDR(sma));
	if (p < (void *)SMA_ADDR(sma) || offset >= sma->size) {
		apc_error("apc_sma_free: could not locate address %p", p);
		return;
	}

	if (!SMA_LOCK(sma)) {
		return;
	}

	sma_deallocate(SMA_HDR(sma), offset);
	SMA_UNLOCK(sma);
#ifdef VALGRIND_FREELIKE_BLOCK
	VALGRIND_FREELIKE_BLOCK(p, 0);
#endif
}

PHP_APCU_API apc_sma_info_t *apc_sma_info(apc_sma_t* sma, zend_bool limited) {

	if (!sma->initialized) {
		return NULL;
	}

	apc_sma_info_t *info = emalloc(sizeof(apc_sma_info_t));
	info->seg_size = sma->size - ALIGNWORD(sizeof(sma_header_t)) - ALIGNWORD(sizeof(block_t));
	info->list = NULL;

	if (limited) {
		return info;
	}

	if (!SMA_LOCK(sma)) {
		efree(info);
		return NULL;
	}

	size_t i;
	sma_header_t *smaheader = SMA_HDR(sma);
	apc_sma_link_t **link = &info->list;

	/* for each free block */
	for (i = 0; i < SMA_BINS; i++) {
		size_t *block_offset = &smaheader->bins[i];
		while (*block_offset) {
			block_t *cur = BLOCKAT(*block_offset);

			CHECK_CANARY(cur);

			*link = emalloc(sizeof(apc_sma_link_t));
			(*link)->size = cur->size;
			(*link)->offset = OFFSET(cur);
			(*link)->next = NULL;
			link = &(*link)->next;

			block_offset = &cur->fnext;
		}
	}

	SMA_UNLOCK(sma);

	return info;
}

PHP_APCU_API void apc_sma_free_info(apc_sma_t *sma, apc_sma_info_t *info) {
	apc_sma_link_t *p = info->list;

	while (p) {
		apc_sma_link_t *q = p;
		p = p->next;
		efree(q);
	}

	efree(info);
}

PHP_APCU_API size_t apc_sma_get_avail_mem(apc_sma_t* sma) {
	return SMA_HDR(sma)->avail;
}

PHP_APCU_API zend_bool apc_sma_check_avail(apc_sma_t *sma, size_t size) {
	return SMA_HDR(sma)->avail >= ALIGNWORD(size + ALIGNWORD(sizeof(block_t)));
}

PHP_APCU_API zend_bool apc_sma_check_avail_contiguous(apc_sma_t *sma, size_t size) {
	size_t realsize = ALIGNWORD(size + ALIGNWORD(sizeof(block_t)));
	sma_header_t *smaheader = SMA_HDR(sma);

	if (!SMA_LOCK(sma)) {
		return 0;
	}

	block_t *cur = bin_find_block(smaheader, realsize);

	SMA_UNLOCK(sma);

	return cur != NULL;
}

PHP_APCU_API void apc_sma_defrag(apc_sma_t *sma, void *data, apc_sma_move_f move) {
	sma_header_t *smaheader = SMA_HDR(sma);
	block_t *cur = BLOCKAT(ALIGNWORD(sizeof(sma_header_t)));
	size_t reclaimed_size = 0;

	if (!SMA_LOCK(sma)) {
		return;
	}

	/* empty all bins */
	size_t i;
	for (i = 0; i < SMA_BINS; i++) {
		smaheader->bins[i] = 0;
	}

	/* loop through all blocks */
	while (cur->size != 0) {
		/* continue until cur points to a free block */
		if (!cur->fprev) {
			cur = NEXT_SBLOCK(cur);
			continue;
		}

		/* if cur is free, nxt must be an allocated block, since we never have two consecutive free blocks */
		block_t *nxt = NEXT_SBLOCK(cur);

		/* if nxt is the last block, or if nxt can't be moved, cur can't be combined with other free blocks */
		if (nxt->size == 0 || !move(data, (char *)nxt + ALIGNWORD(sizeof(block_t)), (char *)cur + ALIGNWORD(sizeof(block_t)))) {
			/* insert cur into the appropriate bin */
			bin_store(smaheader, cur);

			cur->prev_size = 0;
			nxt->prev_size = cur->size;

			cur = NEXT_SBLOCK(nxt);
			continue;
		}

		/* reclaim unused space from the allocated block (nxt->fnext contains the used space) */
		size_t free_size = nxt->size - nxt->fnext;
		reclaimed_size += free_size;
		nxt->size -= free_size;
		free_size += cur->size;

		/* swap cur and nxt by moving nxt (incl. header) and initializing a new block header for cur behind it */
		memmove(cur, nxt, nxt->size);
		cur->prev_size = 0;
		cur = NEXT_SBLOCK(cur);
		cur->size = free_size;
		cur->fprev = 1; /* mark cur as free */

		/* if the next block is also free, combine cur and nxt to one larger free block */
		nxt = NEXT_SBLOCK(cur);
		if (nxt->fprev) {
			cur->size += nxt->size;
		}
	}

	smaheader->avail += reclaimed_size;

	SMA_UNLOCK(sma);
}

/*
 * Local variables:
 * tab-width: 4
 * c-basic-offset: 4
 * End:
 * vim>600: noexpandtab sw=4 ts=4 sts=4 fdm=marker
 * vim<600: noexpandtab sw=4 ts=4 sts=4
 */
