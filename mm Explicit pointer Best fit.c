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
static char *coalesce_next(char *bp, size_t size);
static void chain(char *bp);
static void unchain(char *bp);
static char *find_fit(size_t asize);
static char *place(char *bp, size_t asize);
static void cutblock(char *bp, size_t size, size_t alloc1, size_t alloc2);

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
    // chainstartP의 초기값(= chain의 끝)은 프롤로그 블록의 bp를 포인팅
    chainstartP = heapP + Wsize*2;
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
    char *prev, *next;
    prev = prevblockP(bp);
    next = nextblockP(bp);
    size_t prevalloc = getalloc(footerP(prev));
    size_t nextalloc = getalloc(headerP(next));
    if (!nextalloc)
    {
        unchain(next);
        coalesce_next(bp, getsize(headerP(bp)) + getsize(headerP(next)));
    }
    if (!prevalloc)
    {
        unchain(prev);
        coalesce_next(prev, getsize(headerP(prev)) + getsize(headerP(bp)));
        bp = prev;
    }
    // 기존의 빈 블록들은 unchain했으므로 bp로 합쳐진 새 블록을 chain
    chain(bp);
    return bp;
}

static char *coalesce_next(char *bp, size_t size)
{
    put(headerP(bp), pack(size, 0));
    put(footerP(bp), pack(size, 0));
    return bp;
}

// bp의 크기에 따라 내림차순 chain의 적절한 위치에 배치
// chain 시작 : 가장 최근 등록된 bp / 끝 : 프롤로그 블록
static void chain(char *bp)
{
    size_t size = getsize(headerP(bp));
    char *searchP;
    // chain이 비었거나 chain 내 가장 큰 블록보다 크다면 맨 앞에 배치
    if (chainstartP == heapP - Wsize*2)
    {
        setnextblank(bp, chainstartP);
        setprevblank(chainstartP, bp);
        setprevblank(bp, NULL);
        chainstartP = bp;
    }
    else if (getsize(headerP(chainstartP)) < size)
    {
        setnextblank(bp, chainstartP);
        setprevblank(chainstartP, bp);
        setprevblank(bp, NULL);
        chainstartP = bp;
    }
    // while문으로 size를 비교해가며 위치할 곳을 탐색 후 배치
    else
    {
        searchP = chainstartP;
        while (searchP != heapP - Wsize*2)
        {
            if (getsize(headerP(searchP)) < size)
                break;
            searchP = getnextblank(searchP);
        }
        setprevblank(bp, getprevblank(searchP));
        setnextblank(bp, searchP);
        setprevblank(searchP, bp);
        setnextblank(getprevblank(bp), bp);
    }
}

// bp의 prev와 next를 이음으로써 bp를 unchain
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
    size_t size = getsize(headerP(bp));
    put(headerP(bp), pack(size, 0));
    put(footerP(bp), pack(size, 0));
    coalesce(bp);
}

static char *find_fit(size_t asize)
{
    char *bp;
    bp = chainstartP;
    // chain이 빈 경우 return NULL
    if ((bp == heapP - Wsize*2))
        return NULL;
    // 가장 큰 *chainstartP의 크기보다도 asize가 크다면 탐색하지 않아도 fit이 없음을 알 수 있다
    if (asize > getsize(headerP(bp)))
        return NULL;
    // 크기 내림차순의 chain에서 배치가 불가능한 위치까지 내려가서 그 직전 블록을 할당
    while (bp != heapP - Wsize*2)
    {
        if (getsize(headerP(bp)) < asize)
            break;
        bp = getnextblank(bp);
    }
    return getprevblank(bp);
}

#define placeCUTLINE (1<<6) 
static char *place(char *bp, size_t asize)
{
    size_t csize = getsize(headerP(bp));
    size_t surplus = csize - asize;
    unchain(bp);
    if (surplus < Dsize*2)
    {
        put(headerP(bp), pack(csize, 1));
        put(footerP(bp), pack(csize, 1));
    }
    // find_fit으로 선택된 csize의 빈 블록을 할당에 필요한 asize의 블록과 나머지 빈 조각 surplus로 나눈다
    // surplus가 cutline 이하의 작은 조각이면 asize, surplus 순서로 할당하고,
    // surplus가 cutline 이상의 큰 조각이면 surplus, asize 순서로 할당한다
    // 위의 알고리즘으로 작은 파편은 할당된 블록 뒤에, 큰 파편은 할당된 블록 앞에 오므로
    // place 이후의 파편 coalesce과정에서 큰 파편이 앞 블록의 작은 파편과 합쳐질 기회가 확률적으로 생겨 파편화를 줄인다
    else if (surplus >= placeCUTLINE)
    {
        cutblock(bp, surplus, 0, 1);
        bp = nextblockP(bp);
        coalesce(prevblockP(bp));
    }
    else
    {
        cutblock(bp, asize, 1, 0);
        coalesce(nextblockP(bp));
    }
    return bp;
}

// *bp에 위치한 블록을 둘로 나누는 함수
// 왼쪽 블록의 크기가 입력 size, 각 블록의 alloc은 입력 alloc1, 2의 값을 따른다
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
    if (size == 0)
        return NULL;
    size_t asize;
    asize = Dsize * (1 + (size + Dsize - 1) / Dsize);
    char *bp;
    if ((bp = find_fit(asize)) != NULL)
        return place(bp, asize);
    size_t extendsize = max(asize, CHUNKsize);
    if ((bp = extend_heap(extendsize / Wsize)) == NULL)
        return NULL;
    return place(bp, asize);   
}

#define oversurplusCUTLINE (1<<12)
#define undersurplusCUTLINE (1<<12) 
void *mm_realloc(void *bp, size_t newsize)
{
    if (bp == NULL)
        return mm_malloc(newsize);
    if (newsize == 0)
    {
        mm_free(bp);
        return NULL;
    }
    size_t oldsize = getsize(headerP(bp));
    size_t asize;
    asize = Dsize * (1 + (newsize + Dsize - 1) / Dsize);
    size_t oversize = asize - oldsize;
    char *next;
    next = nextblockP(bp);
    size_t surplus;
    size_t sumsize;
    // oldsize보다 큰 크기를 할당해야한다면 다음 블록을 체크
    // 다음 블록이 비어있고 oversize를 채울 만큼 크다면 그자리서 블록과 병합 후 return bp
    // 이때 안쓰는 공간인 surplus가 cutline 이상이라면 따로 분할해서 빈 블록으로 이용
    if (oversize > 0) 
    {
        surplus = getsize(headerP(next)) - oversize - Dsize*2;
        if (!getalloc(headerP(next)) && surplus > oversurplusCUTLINE)
        {
            unchain(next);
            sumsize = oldsize + getsize(headerP(next));
            put(headerP(bp), pack(sumsize, 1));
            put(footerP(bp), pack(sumsize, 1));
            cutblock(bp, sumsize - surplus, 1, 0);
            chain(nextblockP(bp));
            return bp;
        }
        if (!getalloc(headerP(next)) && surplus > 0)
        {
            unchain(next);
            sumsize = oldsize + getsize(headerP(next));
            put(headerP(bp), pack(sumsize, 1));
            put(footerP(bp), pack(sumsize, 1));
            return bp;
        }
    }
    // oldsize보다 작은 크기를 할당해야한다면 그자리서 return bp
    // 이때 안쓰는 공간인 surplus가 cutline 이상이라면 따로 분할해서 빈 블록으로 이용
    else if (oversize < 0)
    {
        surplus = oldsize - asize;
        if (surplus > undersurplusCUTLINE)
        {
            cutblock(bp, oldsize - surplus, 1, 0);
            chain(nextblockP(bp));
        }
        return bp;
    }
    void *newP;
    newP = mm_malloc(newsize);
    if (newP == NULL)
        return NULL;
    if (newsize < oldsize)
        oldsize = newsize;
    memcpy(newP, bp, oldsize);
    mm_free(bp);
    return newP;
}
