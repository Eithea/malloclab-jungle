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


//////////////////////////////////////////////////////////////////////////////////////////

#define Wsize 4
#define Dsize 8
#define CHUNKsize (1<<8) // 256
#define maxheapsize (20*(1<<20)) // CHUNKsize * 2^12 * 20
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

static size_t measure(size_t size);
static size_t resize(size_t pow2);
static char *extend_heap(size_t size);
static char *coalesce(char *bp);
static char *coalesce_prev(char *prev, char *bp, size_t size);
static void chain(char *bp, size_t order);
static void unchain(char *bp);
static char *find_fit(size_t asize);
static void place(char *bp, size_t asize);

static char *heapP;
static char *chainstart00; // CHUNKsize
// static char *chainstart01; // ~ CHUNKsize * 2^1
// static char *chainstart02; // ~ CHUNKsize * 2^2
// static char *chainstart03; // ~ CHUNKsize * 2^3
// static char *chainstart04; // ~ CHUNKsize * 2^4
// static char *chainstart05; // ~ CHUNKsize * 2^5
// static char *chainstart06; // ~ CHUNKsize * 2^6
// static char *chainstart07; // ~ CHUNKsize * 2^7
// static char *chainstart08; // ~ CHUNKsize * 2^8
// static char *chainstart09; // ~ CHUNKsize * 2^9
// static char *chainstart10; // ~ CHUNKsize * 2^10
// static char *chainstart11; // ~ CHUNKsize * 2^11
// static char *chainstart12; // ~ CHUNKsize * 2^12
// static char *chainstart13; // ~ CHUNKsize * 2^13
// static char *chainstart14; // ~ CHUNKsize * 2^14
// static char *chainstart15; // ~

static size_t measure(size_t size)
{
    size_t pow2 = 0;
    while (CHUNKsize < size)
    {
        size = size / 2;
        pow2 = pow2 + 1;
    }
    return pow2;
}

static size_t resize(size_t pow2)
{
    size_t size = CHUNKsize;
    while (pow2)
    {
        size = size * 2;
        pow2 = pow2 - 1;
    }
    return size;
}

int mm_init(void)
{
    // Explicit??? 4?????? ?????? 6?????? ??? heap??? ??????
    if ((heapP = mem_sbrk(Wsize*20)) == (void*)-1)
        return -1;
    put(heapP, 0);
    put(heapP + Wsize, pack(Dsize*2, 1));
    put(heapP + Wsize*2, 0);
    put(heapP + Wsize*3, 0);
    put(heapP + Wsize*18, pack(Dsize*2, 1));
    put(heapP + Wsize*19, pack(0, 1));
    chainstart00 = heapP + Wsize*2;
    // chainstartXX = chainstart00 + Wsize * XX (XX = measure(size))
    heapP = heapP + Wsize*18;
    // extend_heap??? ?????? CH*2^n????????? ??? ????????????, word??? ?????? mod??? ????????? ??????
    if (extend_heap(CHUNKsize) == NULL)
        return -1;
    return 0;
}

static char *extend_heap(size_t size)
{
    // input?????? size ????????? ?????? ????????? CH*2^n ????????? resize
    size_t pow2 = measure(size);
    size = resize(pow2);
    char *bp;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    put(headerP(bp), pack(size, 0));
    put(footerP(bp), pack(size, 0));
    put(headerP(nextblockP(bp)), pack(0, 1));
    return coalesce(bp);
}

static char *coalesce(char *bp)
{
    char *prev, *next;
    size_t prevalloc, nextalloc, size, prevsize, nextsize;
    while (1)
    {
        prev = prevblockP(bp);
        next = nextblockP(bp);
        prevalloc = getalloc(footerP(prev));
        nextalloc = getalloc(headerP(next));
        size = getsize(headerP(bp));
        prevsize = getsize(headerP(prev));
        nextsize = getsize(headerP(next));
        // ?????? or ?????? ????????? ???????????? ????????? ????????? ??????
        // ??????/?????? ?????? ????????? ???????????????????????? ??????
        if (size == nextsize && !nextalloc)
        {
            unchain(next);
            bp = coalesce_prev(bp, next, size);
        }
        else if (prevsize == size && !prevalloc)
        {
            unchain(prev);
            bp = coalesce_prev(prev, bp, size);
        }
        else
            break;
    }
    // while?????? ???????????? ????????? ?????? ????????? ?????? bp??? chain
    chain(bp);
}

static char *coalesce_prev(char *prev, char *bp, size_t size)
{
    size = size * 2;
    put(headerP(prev), pack(size, 0));
    put(footerP(bp), pack(size, 0));
    return prev;
}


static void chain(char *bp, size_t order)
{
    setnextblank(bp, chainstartP);
    setprevblank(chainstartP, bp);
    setprevblank(bp, NULL);
    chainstartP = bp;
}

static void unchain(char *bp)
{
    if (getprevblank(bp))
        setnextblank(getprevblank(bp), getnextblank(bp));
    else
        chainstartP = getnextblank(bp);
    setprevblank(getnextblank(bp), getprevblank(bp));
}

void mm_free(void *bp)
{
    // ???????????? ????????? ????????? ????????? ??? ????????????, ????????? alloc?????? 0?????? ????????? ???????????? ????????????
    size_t size = getsize(headerP(bp));
    put(headerP(bp), pack(size, 0));
    put(footerP(bp), pack(size, 0));
    // ?????? ??? ???????????? ??????
    coalesce(bp);
}

static char *find_fit(size_t asize)
{
    
    char *bp;
    // chainstartP?????? ??????
    // bp = getnextblankP(bp) ????????????
    for (bp = chainstartP; getalloc(headerP(bp)) == 0; bp = getnextblank(bp))
    {
        if (getsize(headerP(bp)) >= asize)
        {
            return bp;
        }
    }
    return NULL;
}

static void place(char *bp, size_t asize)
{
    // ??? ???????????? ????????? ???????????? ?????? bp??? unchain?????? ??? ????????? Inplicit??? ??????
    size_t csize = getsize(headerP(bp));
    size_t surplus = csize - asize;
    if (surplus < Dsize*2)
    {
        put(headerP(bp), pack(csize, 1));
        put(footerP(bp), pack(csize, 1));
        unchain(bp);
    }
    else
    {
        put(headerP(bp), pack(asize, 1));
        put(footerP(bp), pack(asize, 1));
        unchain(bp);
        bp = nextblockP(bp);
        put(headerP(bp), pack(surplus, 0));
        put(footerP(bp), pack(surplus, 0));
        coalesce(bp);
    }
}

void *mm_malloc(size_t size)
{
    if (size == 0)
        return NULL;
    size_t asize;
    asize = Dsize * ((size + Dsize - 1) / Dsize);
    asize = asize + Dsize;
    char *bp;
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    size_t extendsize = max(asize, CHUNKsize);
    if ((bp = extend_heap(extendsize / Wsize)) == NULL)
        return NULL;
    place(bp, asize);
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
    size_t oldsize = getsize(headerP(oldP));
    void *newP;
    newP = mm_malloc(newsize);
    if (newP == NULL)
        return NULL;
    if (newsize < oldsize)
        oldsize = newsize;
    memcpy(newP, oldP, oldsize);
    mm_free(oldP);
    return newP;
}
