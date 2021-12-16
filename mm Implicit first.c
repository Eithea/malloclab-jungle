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
// heap 확장의 최소단위 CHUNKsize 설정
// 매 확장마다 딱 필요한만큼만 확장한다면 너무 작은 크기의 확장을 반복시 연산력의 낭비가 된다
// 필요한 메모리가 CHUNKsize 이하이면 CHUNKsize만큼 확장할 것
#define CHUNKsize (1<<8)

#define max(x, y) ((x) > (y) ? (x) : (y))
#define get(p) (*(unsigned int *)(p))
#define put(p, val) (*(unsigned int *)(p) = (val))

// size부와 alloc부를 하나로 합친다
// 2진화 size의 e0자리는 항상 0이므로 이곳에 alloc을 기록할 수 있다
#define pack(size, alloc) ((size) | (alloc))

// pack(size, alloc)의 e2자리까지를 날림으로써 8의배수로 만들어 size부를 취함
#define getsize(p) (get(p) & ~0x7)
// pack(size, alloc)의 e0자리만 남겨 alloc부를 취함
#define getalloc(p) (get(p) & 0x1)

// 블록의 시작점 한칸 앞은 headerP
#define headerP(bp) ((char *)(bp) - Wsize)
// 블록의 시작점에서 블록의 size만큼 전진 후 2칸 후진하면 블록의 footerP
#define footerP(bp) ((char *)(bp) + getsize(headerP(bp)) - Dsize)
// 블록의 시작점에서 headerP의 size만큼 전진하면 다음 블록의 시작점 (headerP가 다음 블록을 가리키므로)
#define nextblockP(bp) ((char *)(bp) + getsize(headerP(bp)))
// 블록의 시작점에서 이전 블록의 size만큼 후진하면 이전 블록의 시작점
// headerP(bp)의 한칸 앞은 이전 블록의 footerP이므로 이것을 getsize하면 이전 블록의 size가 리턴됨 
#define prevblockP(bp) ((char *)(bp) - getsize(headerP(bp) - Wsize))

static char *heapP;
static char *extend_heap(size_t);
static char *coalesce(char *);
static char *find_fit(size_t);
static void place(char *, size_t);

int mm_init(void)
{
    // mem_sbrk를 호출하여 4칸의 새 heap을 생성
    // mem_sbrk(x)는 heap의 끝을 가리키는 포인터 mem_brk를 x만큼 전진시켜 기존 mem_brk 이후의 미할당된 가상메모리를 할당된 빈 공간으로 바꿈
    if ((heapP = mem_sbrk(Wsize*4)) == (void*)-1)
        return -1;
    // 주어진 초기 4칸에 heap start(=0), 한쌍의 header&footerP(프롤로그 블록), heap end(=pack(0, 1))를 기록
    put(heapP, 0);
    put(heapP + Wsize, pack(Dsize, 1));
    put(heapP + Wsize*2, pack(Dsize, 1));
    put(heapP + Wsize*3, pack(0, 1));
    // heapP를 2칸 이동해서 프롤로그 블록을 포인팅
    heapP = heapP + Wsize*2;
    // extend_heap, coalesce가 차례로 실행되며 heap을 CHUNKsize만큼 확장
    if (extend_heap(CHUNKsize / Wsize) == NULL)
        return -1;
    // 상단부 heapP 포인팅이나 extend_heap에서 메모리 부족으로 mem_sbrk가 할당 실패시 return -1, 정상작동시 return 0
    return 0;
}

static char *extend_heap(size_t words)
{
    // size는 words개의 Wsize를 담을 수 있는 최소 Dsize*n (짝수개의 Wsize 칸)
    // size를 항상 짝수로 함으로써 8비트 포인터의 e0자리에 alloc 여부(0, 1)를 기록 가능
    size_t size = (words % 2) ? Wsize * (words + 1) : Wsize * words;
    // size만큼의 새 가상메모리 할당 실패시 return NULL, 성공시 bp에 새로 받은 블록을 포인팅 후 이후 진행
    char *bp;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    // 빈 블록의 끝단에 header&footerP 기록
    // header&footerP에 기록된 pack(size, 0)는 size만큼의 공간이 비었음을 의미 
    put(headerP(bp), pack(size, 0));
    put(footerP(bp), pack(size, 0));
    // 새 블록만큼 heap이 확장되었으므로 그 다음칸에 heap end(=pack(0, 1)) 갱신
    // 새로 생긴 마지막 블록을 포인팅하는 bp에서 nextblockP(bp)를 쓰면 마지막 블록 다음의 빈 공간이 나올 것
    put(headerP(nextblockP(bp)), pack(0, 1));
    // bp의 주변 블록과의 병합을 시도하는 함수 coalesce 실행
    return coalesce(bp);
    // 이전 블록이 비어는 있지만 size가 모자른 경우에도 extend_heap이 실행될 것이므로, 이전 블록과의 병합을 시도해야 파편화를 줄일 수 있음
}

static char *coalesce(char *bp)
{
    char *prev;
    char *next;
    prev = prevblockP(bp);
    next = nextblockP(bp);
    // getalloc함수를 *bp의 앞, 뒤 블록에 대해 사용하여 할당 여부를 확인
    // prevalloc, nextalloc 각 블록이 미할당시 0, 할당시 1
    size_t prevalloc = getalloc(footerP(prev));
    size_t nextalloc = getalloc(headerP(next));
    size_t size = getsize(headerP(bp));
    // *bp가 마지막 블록일 경우 next가 heap end를 리턴하고 이는 pack(0, 1)이므로 next가 1이 된다)
    // *bp가 첫 블록일 경우 prev가 프롤로그 블록 pack(Dsize, 1)를 리턴하므로 prev가 1이 된다

    // 빈 블록이 없다면 return
    if (prevalloc && nextalloc)
        return bp;
    // 뒷 블록만 비어있다면 이와 병합
    if (prevalloc && !nextalloc)
    {
        // 합친 블록의 크기는 두 블록의 size의 합
        size = size + getsize(headerP(next));
        // *bp의 headerP에 size 정보를 갱신
        put(headerP(bp), pack(size, 0));
        // **next의 footerP에 size 정보를 갱신
        // headerP(bp)가 갱신되었으므로 footerP(bp)는 *bp의 footer가 아닌 *next의 footer를 가리킨다
        put(footerP(bp), pack(size, 0));
    }
    // 앞 블록만 비어있다면 이와 병합
    else if (!prevalloc && nextalloc)
    {
        // 합친 블록의 크기는 두 블록의 size의 합
        size = size + getsize(headerP(prev));
        // *prev의 headerP에 size 정보를 갱신
        put(headerP(prev), pack(size, 0));
        // *bp의 footerP에 size 정보를 갱신
        put(footerP(bp), pack(size, 0));
        // 둘을 합친 블록의 시작점은 *prev의 시작점이므로 bp의 포인팅을 *prev로 변경
        bp = prev;
    }
    // 앞, 뒤 블록 모두 비어있다면 셋 병합
    else
    {
        // 합친 블록의 크기는 세 블록의 size의 합
        size = size + getsize(headerP(prev)) + getsize(headerP(next));
        // *prev의 headerP에 size 정보를 갱신
        put(headerP(prev), pack(size, 0));
        // **next의 footerP에 size 정보를 갱신
        put(footerP(next), pack(size, 0));
        // 셋을 합친 블록의 시작점은 *prev의 시작점이므로 bp의 포인팅을 *prev로 변경
        bp = prev;
    }
    return bp;
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
    // 프롤로그 블록에서 시작
    // *bp가 비어있고 size가 입력값 asize 이상이라면 return bp
    // 아니라면 bp = nextblockP(bp)
    for (bp = heapP; getsize(headerP(bp)) > 0; bp = nextblockP(bp))
    {
        if (!getalloc(headerP(bp)) && (getsize(headerP(bp)) >= asize))
        {
            return bp;
        }
    }
    return NULL;
}

static void place(char *bp, size_t asize)
{
    // find_fit으로 리턴받은 블록의 크기 csize와 데이터를 채울 크기 asize를 비교
    size_t csize = getsize(headerP(bp));
    size_t surplus = csize - asize;
    // 잉여공간이 3칸 이하(surplus < 2Dsize)라면 분할하더라도 header&footerP 채우고 나면 Dsize 하나도 안남는다
    // 따라서 cisze 전체를 다 사용
    if (surplus < Dsize*2)
    {
        put(headerP(bp), pack(csize, 1));
        put(footerP(bp), pack(csize, 1));
    }
    // 잉여공간이 그 이상이라면 잉여를 분할시 1Dsize 이상의 가용가능
    // asize만큼만의 공간을 사용하고 잉여를 새 빈 블록으로 분할
    else
    {
        put(headerP(bp), pack(asize, 1));
        put(footerP(bp), pack(asize, 1));
        bp = nextblockP(bp);
        put(headerP(bp), pack(surplus, 0));
        put(footerP(bp), pack(surplus, 0));
    }
}

void *mm_malloc(size_t size)
{
    // size가 0이라면 return
    if (size == 0)
        return NULL;
    // asize는 size를 담을 수 있는 가장 작은 Dsize로 한다
    size_t asize;
    asize = Dsize * ((size + Dsize - 1) / Dsize);
    // header&footerP에 쓸 Dsize 하나 추가
    asize = asize + Dsize;
    // find_fit 결과 asize 이상의 블록을 할당가능하다면 할당 후 return bp;
    char *bp;
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    // 할당가능한 asize 이상의 블록이 없다면 asize의 크기에 따라 extendsize를 결정
    size_t extendsize = max(asize, CHUNKsize);
    // extendsize만큼의 extend_heap이 성공했다면 할당 후 return bp;
    if ((bp = extend_heap(extendsize / Wsize)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void *mm_realloc(void *oldP, size_t newsize)
{
    // oldP가 입력되지 않았다면 malloc과 같은 기능
    if (oldP == NULL)
        return mm_malloc(newsize);
    // newsize가 0이라면 free와 같은 기능
    if (newsize == 0)
    {
        mm_free(oldP);
        return NULL;
    }
    // 그 외의 경우 재할당 진행
    void *newP;
    newP = mm_malloc(newsize);
    // newsize만큼의 할당에 실패하면 return NULL
    if (newP == NULL)
        return NULL;
    // 성공시 newP에 oldP의 데이터를 oldsize만큼 memory copy
    // newsize가 oldsize보다 작다면 newsize만큼의 데이터만 담는다
    size_t oldsize = getsize(headerP(oldP));
    if (newsize < oldsize)
        oldsize = newsize;
    memcpy(newP, oldP, oldsize);
    // oldP는 free, return newP
    mm_free(oldP);
    return newP;
}
