/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    "jungle",
    "Jihun Kim",
    "e@mail.com",
    "",
    ""
};
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


//////////////////////////////////////////////////////////////////////////////////////////////////////

#define Wsize 4
#define Dsize 8
#define CHUNKsize (1<<7) 
#define max(x, y) ((x) > (y) ? (x) : (y))
#define get(p) (*(unsigned int *)(p))
#define put(p, val) (*(unsigned int *)(p) = (val))
#define pack(size, alloc) ((size) | (alloc))
#define getsize(p) (get(p) & ~0x7)
#define getalloc(p) (get(p) & 0x1)
#define headerP(bp) ((char *)(bp) - Wsize)
#define footerP(bp) ((char *)(bp) + getsize(headerP(bp)) - Dsize)
#define nextblockP(bp) ((char *)(bp) + getsize(headerP(bp)))
#define prevblockP(bp) ((char *)(bp) - getsize(headerP(bp) - Wsize))

#define getprevblank(bp) (*(char **)(bp + Wsize))
#define getnextblank(bp) (*(char **)(bp))
#define setprevblank(bp, x) (getprevblank(bp) = (x))
#define setnextblank(bp, x) (getnextblank(bp) = (x))



static char *extend_heap(size_t words);
static char *coalesce(char *bp);
static char *coalesce_next(char *bp, size_t size);
static void chain(char *bp, size_t size);
static void unchain(char *bp, size_t size);
static char *find_fit(size_t asize);
static char *place(char *bp, size_t asize);
static void cutblock(char *bp, size_t size, size_t alloc1, size_t alloc2);

static size_t measure_order(size_t size);
static size_t resize(size_t p2);


static char *chainstart_order0;
static char *heapP;
#define max_chainorder 30
int mm_init(void)
{
    if ((heapP = mem_sbrk(Wsize*(4 + max_chainorder))) == (void*)-1)
        return -1;
    put(heapP, 0);
    put(heapP + Wsize, pack(Wsize*(2 + max_chainorder), 1));
    size_t i;
    for (i = 2; i < 2 + max_chainorder; i = i + 1)
    {
        put(heapP + Wsize*i, 0);
        i = i + 1;
    }
    put(heapP + Wsize*(2 + max_chainorder), pack(Wsize*(2 + max_chainorder), 1));
    put(heapP + Wsize*(3 + max_chainorder), pack(0, 1));
    chainstart_order0 = heapP + Wsize*2;
    // chainstart_orderX = chainstart_order0 + Wsize*X;
    // max_chainorder개의 가용리스트의 start 포인터를 프롤로그 블록에서 관리
    heapP = heapP + Wsize*(2 + max_chainorder);
    if (extend_heap(CHUNKsize) == NULL)
        return -1;
    return 0;
}

static size_t measure_order(size_t size)
{
    size_t p2 = 0;
    size_t size2 = 1;
    while (size2 < size)
    {
        size2 = size2 * 2;
        p2 = p2 + 1;
    }
    return p2;
}

static size_t resize(size_t p2)
{
    size_t size2 = 1;
    while (p2)
    {
        size2 = size2 * 2;
        p2 = p2 - 1;
    }
    return size2;
}

// 입력 size2는 항상 2의 제곱수로 인풋
static char *extend_heap(size_t size2)
{
    char *bp;
    if ((long)(bp = mem_sbrk(size2)) == -1)
        return NULL;
    put(headerP(bp), pack(size2, 0));
    put(footerP(bp), pack(size2, 0));
    put(headerP(nextblockP(bp)), pack(0, 1));
    return coalesce(bp);
}

static char *coalesce(char *bp)
{
    char *prev, *next;
    prev = prevblockP(bp);
    next = nextblockP(bp);
    size_t prevalloc = getalloc(footerP(prev));
    size_t nextalloc = getalloc(headerP(next));
    size_t size = getsize(headerP(bp));
    // bp와 size가 다르다면, alloc 여부에 관계없이 병합하지 않으므로 1로 수정
    if (size != getsize(headerP(prev)))
        prevalloc = 1;
    if (size != getsize(headerP(next)))
        nextalloc = 1;
    while (!(prevalloc && nextalloc))
    {
        if (prevalloc && !nextalloc)
        {
            unchain(next, size);
            coalesce_next(bp, size*2);
        }
        else if (!prevalloc && nextalloc)
        {
            unchain(prev, size);
            coalesce_next(prev, size*2);
            bp = prev;
        }
        prev = prevblockP(bp);
        next = nextblockP(bp);
        prevalloc = getalloc(footerP(prev));
        nextalloc = getalloc(headerP(next));
        if (size != getsize(headerP(prev)))
            prevalloc = 1;
        if (size != getsize(headerP(next)))
            nextalloc = 1;
        size = getsize(headerP(bp));
    }
    chain(bp, size);
    return bp;
}

static char *coalesce_next(char *bp, size_t size)
{
    put(headerP(bp), pack(size, 0));
    put(footerP(nextblockP(bp)), pack(size, 0));
    return bp;
}

static void chain(char *bp, size_t size)
{
    char *chainstartP;
    size_t order = measure_order(size);
    if (!getsize(chainstart_order0 + Wsize*order))
    {
        setnextblank(bp, NULL);
        setprevblank(bp, NULL);
        setnextblank(chainstart_order0 + Wsize*order, bp);
    }
    else
    {
    chainstartP = getnextblank(chainstart_order0 + Wsize*order);
    setnextblank(bp, chainstartP);
    setprevblank(chainstartP, bp);
    setprevblank(bp, NULL);
    setnextblank(chainstart_order0 + Wsize*order, bp);
    }
}

static void unchain(char *bp, size_t size)
{
    char *chainstartP;
    size_t order = measure_order(size);
    chainstartP = getnextblank(chainstart_order0 + Wsize*order);
    if (getprevblank(bp))
    {
        setnextblank(getprevblank(bp), getnextblank(bp));
        setprevblank(getnextblank(bp), getprevblank(bp));
    }
    else if (getnextblank(bp))
    {
        setnextblank(chainstart_order0 + Wsize*order, getnextblank(bp));
        setprevblank(getnextblank(bp), NULL);
    }
    else
    {
        put(chainstart_order0 + Wsize*order, 0);
    }
}

void mm_free(void *bp)
{
    size_t size = getsize(headerP(bp));
    put(headerP(bp), pack(size, 0));
    put(footerP(bp), pack(size, 0));
    coalesce(bp);
}

static char *find_fit(size_t asize)
{
    char *bp;
    char *chainstartP;
    size_t order = measure_order(asize);
    if (order >= max_chainorder)
        return NULL;
    if (!getsize(chainstart_order0 + Wsize*order))
        return find_fit(asize*2);
    chainstartP = getnextblank(chainstart_order0 + Wsize*order);
    // chainstartP에서 시작
    // bp = getnextblankP(bp) 반복탐색
    for (bp = chainstartP; bp != NULL; bp = getnextblank(bp))
    {
        if (getsize(headerP(bp)) >= asize)
        {
            return bp;
        }
    }
    return find_fit(asize*2);
}

static char *place(char *bp, size_t asize)
{
    size_t csize = getsize(headerP(bp));
    unchain(bp, csize);
    if (csize < asize*2)
    {
        put(headerP(bp), pack(csize, 1));
        put(footerP(bp), pack(csize, 1));
    }
    else
    {
        while (csize >= asize*2)
        {
        cutblock(bp, csize / 2, 1, 0);
        coalesce(nextblockP(bp));
        csize = csize / 2;
        }
    }
    return bp;
}

static void cutblock(char *bp, size_t size, size_t alloc1, size_t alloc2)
{
    size_t csize = getsize(headerP(bp));  
    put(headerP(bp), pack(size, alloc1));
    put(footerP(bp), pack(size, alloc1));
    put(headerP(nextblockP(bp)), pack(csize-size, alloc2));
    put(footerP(nextblockP(bp)), pack(csize-size, alloc2));
}

void *mm_malloc(size_t size)
{
    // printf("malloc %d\n", size);
    if (size == 0)
        return NULL;
    size_t p2 = measure_order(Dsize * (1 + (size + Dsize - 1) / Dsize));
    size_t asize = resize(p2);
    char *bp;
    if ((bp = find_fit(asize)) != NULL)
    {
        bp = place(bp, asize);
        return bp;
    }
    size_t extendsize = max(asize, CHUNKsize);
    if ((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    bp = place(bp, asize);
    return bp;
}

void *mm_realloc(void *oldP, size_t newsize)
{
    if (oldP == NULL)
        return mm_malloc(newsize);
    if (newsize == 0)
    {
        mm_free(oldP);
        return NULL;
    }
    char *newP;
    newP = mm_malloc(newsize);
    if (newP == NULL)
        return NULL;
    size_t oldsize = getsize(headerP(oldP));
    if (newsize < oldsize)
        oldsize = newsize;
    memcpy(newP, oldP, oldsize);
    mm_free(oldP);
    return newP;
}