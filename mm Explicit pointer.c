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

#define Wsize 4 /* char 한칸 */
#define Dsize 8 /* char 두칸 */
#define CHUNKsize (1<<12) 
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

// 모든 빈 블록은 bp와 bp 다음 칸이 비어있다 (Dsize단위의 할당이므로)
// 빈 블록은 bp자리에 이전 빈 블록의 포인터를, bp 다음자리에는 다음 빈 블록의 포인터를 기록
// 이것들의 값을 취해 쓰는것으로 이전, 다음 빈 블록으로 이동 가능
#define getprevblank(bp) (*(char **)(bp))
#define getnextblank(bp) (*(char **)(bp + Wsize))
#define setprevblank(bp, x) (getprevblank(bp) = (x))
#define setnextblank(bp, x) (getnextblank(bp) = (x))


static char *chainstartP;
static char *heapP;

static char *extend_heap(size_t words);
static char *coalesce(char *bp);
static void chain(char *bp);
static void unchain(char *bp);
static char *find_fit(size_t asize);
static void place(char *bp, size_t asize);

int mm_init(void)
{
    // Explicit은 4칸이 아닌 6칸의 새 heap을 생성
    if ((heapP = mem_sbrk(Wsize*6)) == (void*)-1)
        return -1;
    put(heapP, 0);
    put(heapP + Wsize, pack(Dsize*2, 1));
    put(heapP + Wsize*2, 0);
    put(heapP + Wsize*3, 0);
    put(heapP + Wsize*4, pack(Dsize*2, 1));
    put(heapP + Wsize*5, pack(0, 1));
    // 프롤로그 블록에 빈칸을 만들어 blank들의 chain을 관리
    // chainstart의 초기값은 프롤로그 블록의 bp를 포인팅
    chainstartP = heapP + Wsize*2;
    // heapP 위치
    heapP = heapP + Wsize*4;
    if (extend_heap(CHUNKsize / Wsize) == NULL)
        return -1;
    return 0;
}

static char *extend_heap(size_t words)
{
    size_t size = (words % 2) ? Wsize * (words + 1) : Wsize * words;
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
    char *prev;
    char *next;
    prev = prevblockP(bp);
    next = nextblockP(bp);
    size_t prevalloc = getalloc(footerP(prev));
    size_t nextalloc = getalloc(headerP(next));
    size_t size = getsize(headerP(bp));
    
    if (prevalloc && !nextalloc)
    {
        // next를 blank chain에서 제거, 이후 Implicit과 같은 병합 절차 진행
        unchain(next);
        size = size + getsize(headerP(next));
        put(headerP(bp), pack(size, 0));
        put(footerP(bp), pack(size, 0));
    }
    else if (!prevalloc && nextalloc)
    {
        // prev를 blank chain에서 제거, 이후 Implicit과 같은 병합 절차 진행
        unchain(prev);
        size = size + getsize(headerP(prev));
        put(headerP(prev), pack(size, 0));
        put(footerP(bp), pack(size, 0));
        bp = prev;
    }
    else if (!prevalloc && !nextalloc)
    {
        // prev, next를 blank chain에서 제거, 이후 Implicit과 같은 병합 절차 진행
        unchain(prev);
        unchain(next);
        size = size + getsize(headerP(prev)) + getsize(headerP(next));
        put(headerP(prev), pack(size, 0));
        put(footerP(next), pack(size, 0));
        bp = prev;
    }
    // 기존의 빈 블록들은 unchain했으므로 bp로 합쳐진 새 블록을 chain
    chain(bp);
    return bp;
}

static void chain(char *bp)
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
    // 데이터는 지우지 않아도 덮어쓸 수 있으므로, 블록의 alloc부를 0으로 바꾸는 것만으로 충분하다
    size_t size = getsize(headerP(bp));
    put(headerP(bp), pack(size, 0));
    put(footerP(bp), pack(size, 0));
    // 주변 빈 블록과의 병합
    coalesce(bp);
}

static char *find_fit(size_t asize)
{
    
    char *bp;
    // chainstartP에서 시작
    // bp = getnextblankP(bp) 반복탐색
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
    // 빈 블록에서 할당된 블록으로 바뀐 bp를 unchain하는 것 외에는 Inplicit과 같다
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
