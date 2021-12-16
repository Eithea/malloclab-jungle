/*
 *  Segregated free list로 구현한 malloc 프로토 타입.
 *  카네기 멜론 대학의 과제에는 금지되어있는 배열을 전역변수로 선언한 상태의 프로토타입니다.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "Enter the dragon",
    /* First member's full name */
    "D.T.",
    /* First member's email address */
    "dt@swjungle.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* 주소를 워드(4)로 정렬할지 더블 워드(8)로 정렬 할지 결정한다 */
#define ALIGNMENT 8

/* 받은 주소가 워드의 배수가 되도록 만든다 */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본적인 상수와 매크로*/
#define WSIZE   4           //워드의 크기(바이트)
#define DSIZE   8           //더블워드의 크기(바이트)
#define CHUNKSIZE (1<<12)   //힙 영역을 한 번 늘릴 때 마다 늘려 줄 크기
#define LISTLIMIT 20        //리스트의 최대 길이

#define MAX(x, y) ((x)>(y)?(x):(y))

/* 크기와 할당 상태를 1워드로 묶는다 */
#define PACK(size, alloc) ((size)|(alloc))

/* 주소 p에 있는 값을 읽고 쓴다 */
#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에서 블록의 크기와 할당상태를 읽어온다 */
#define GET_SIZE(p)     (GET(p)&~0x7)
#define GET_ALLOC(p)    (GET(p)&0x1)

/* 블록 포인터 bp를 받으면, 그 블록의 헤더와 풋터 주소를 반환한다 */
#define HDRP(bp) ((char *)(bp) - WSIZE) 
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* 블록 포인터 bp를 받으면, 그 이전 블록과 이후의 블록의 주소를 반환한다 */
#define SUCC_P_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PRED_P_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 블록 안에 저장된 리스트 이전 블록과 리스트 이후 블록의 주소를 가져온다. */
#define SUCC_P(bp)  (*(char **)(bp))
#define PRED_P(bp)  (*(char **)((bp)+WSIZE))

static void *heap_listp;                    //가상 메모리의 시작이 될 주소
static void *free_list[LISTLIMIT];          //가용 메모리의 리스트를 저장할 주소

static void *coalesce(void *bp);            //가용해진 블럭들을 합쳐주는 함수
static void *extend_heap(size_t words);     //가용 영역이 부족할 때 추가로 힙 영역을 요청하는 함수
static void *find_fit(size_t asize);        //메모리를 할당하기에 충분한 공간을 가진 블록을 찾는 함수
static void place(void *p, size_t size);    //메모리를 할당하고 남은 공간을 분리해주는 함수
static void list_add(void *p);              //가용 블록을 가용블록 리스트에 추가하는 함수
static void list_remove(void *p);           //가용 블록을 가용블록 리스트에서 제거해주는 함수

/* 
 * mm_init - 말록을 초기화
 */

int mm_init(void) {

    //리스트를 만든 곳에 쓰레기 값이 들어있지 않도록 초기화 해준다.
    for (int i = 0; i < LISTLIMIT; i++){
        free_list[i] = NULL;
    }

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0,1));

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size = (words%2) ? (words+1)*WSIZE : words*WSIZE;

    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(SUCC_P_BLKP(bp)), PACK(0,1));
    list_add(bp);

    return coalesce(bp);
}

/* 
 * mm_malloc - 메모리를 할당하고 필요하면 힙영역을 확장해달라고 요청한다
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size<=DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE);

    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize){
    // Search for free block in segregated list
    size_t searchsize = asize;          //사이즈 값 변형을 위해 새로운 변수 선언 
    char *ptr;                          //탐색을 위한 포인터
    int index = 0; 
    while (index < LISTLIMIT) {
        if ((index == LISTLIMIT - 1) || ((searchsize <= 1) && (free_list[index] != NULL))) {
            //^리스트의 마지막에 도착하거나     ^원하는 크기 범위의 블럭들이 들어있는 비어있지 않은 리스트임이 확인되면
            ptr = free_list[index];                                     //리스트의 원소들을 검색한다
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))))){
                ptr = SUCC_P(ptr);
            }               //리스트가 비어있지 않지만, 사이즈가 작다면 리스트의 다음 원소로 이동한다
            if (ptr != NULL)
                return ptr;       //리스트 끝까지 확인했는데 맞는게 없는 것이 아니라면 값을 반환한다
        }
        searchsize >>= 1;          //비트 연산을 통해 블록의 사이즈에 적절한 인덱스를 확인한다
        index++;
    }
    return NULL;
}

/*
 * place - 가상 메모리 공간을 할당하고 크기에 따라 새로운 가용 블럭을 만든다.
 */
static void place(void *p, size_t size){
    size_t free_block = GET_SIZE(HDRP(p));
    list_remove(p);
    if ((free_block-size)>=(2*DSIZE)){
        PUT(HDRP(p), PACK(size, 1));
        PUT(FTRP(p), PACK(size, 1));
        p = SUCC_P_BLKP(p);
        PUT(HDRP(p), PACK(free_block-size, 0));
        PUT(FTRP(p), PACK(free_block-size, 0));
        list_add(p);
    } else {
    PUT(HDRP(p), PACK(free_block, 1));
    PUT(FTRP(p), PACK(free_block, 1));
    }
}

/*
 * list_add - 가용블럭 리스트에 새로운 블럭의 정보를 넣는다.
 */
static void list_add(void *p){
    size_t size = GET_SIZE(HDRP(p));
    int index = 0;
    void *insert_p = NULL; //블럭이 삽입될 위치를 나타내는 포인터

    //블럭이 삽입될 인덱스를 검색한다.
    while ((index < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        index++;
    }
    //리스트를 블럭의 크기별로 오름차순 시켜주기 위해 자리를 검색한다.
    void *search_p = free_list[index];
    while ((search_p != NULL) && (size > GET_SIZE(HDRP(search_p)))) {
        insert_p = search_p;
        search_p = SUCC_P(search_p);
    }
    // 적절한 위치를 찾으면 주소를 저장해준다.
    if (search_p != NULL) {
        if (insert_p != NULL) {
            SUCC_P(p) = PRED_P(search_p);
            PRED_P(search_p) = p;
            PRED_P(p) = insert_p;
            SUCC_P(insert_p) = p;
        } else {
            SUCC_P(p) = search_p;
            PRED_P(search_p)= p;
            PRED_P(p) = NULL;
            free_list[index] = p;
        }
    } else {
        if (insert_p != NULL) {
            SUCC_P(p) =  NULL;
            PRED_P(p) = insert_p;
            SUCC_P(insert_p) = p;
        } else {
            SUCC_P(p) = NULL;
            PRED_P(p) = NULL;
            free_list[index] = p;
        }
    }
    return;
}

/*
 * list_remove - 가용블럭 리스트에서 블럭의 정보를 제거한다
 */
static void list_remove(void *p){
    size_t size = GET_SIZE(HDRP(p));
    int index = 0;
    // Select segregated list 
    while ((index < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        index++;
    }

    if (SUCC_P(p) != NULL) {
        if (PRED_P(p) != NULL) {
            PRED_P(SUCC_P(p)) = PRED_P(p);
            SUCC_P(PRED_P(p)) = SUCC_P(p);
        } else {
            PRED_P(SUCC_P(p)) = NULL;
            free_list[index] = SUCC_P(p);
        }
    } else {
        if (PRED_P(p) != NULL) {
            SUCC_P(PRED_P(p)) = NULL;
        } else {
            free_list[index] = NULL;
        }
    }

    return;
}

/*
 * mm_free - 사용하지 않게 된 메모리를 반환한다.
 */
void mm_free(void *ptr){
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    list_add(ptr);
    coalesce(ptr);
}

/*
 * coalesce - 가용블럭들이 파편화 되지 않도록 하나도 합쳐준다.
 */
static void *coalesce(void *bp){
    size_t PRED_P_alloc = GET_ALLOC(FTRP(PRED_P_BLKP(bp)));
    size_t SUCC_P_alloc = GET_ALLOC(HDRP(SUCC_P_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //기존의 블럭을 리스트에서 제거한다
    list_remove(bp);

    //조건에 따라 새로운 블럭을 생성한다.
    if(PRED_P_alloc && !SUCC_P_alloc){
        list_remove(SUCC_P_BLKP(bp));
        size += GET_SIZE(HDRP(SUCC_P_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!PRED_P_alloc && SUCC_P_alloc){
        list_remove(PRED_P_BLKP(bp));
        size += GET_SIZE(HDRP(PRED_P_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PRED_P_BLKP(bp)), PACK(size, 0));
        bp = PRED_P_BLKP(bp);
    } else if (!PRED_P_alloc && !SUCC_P_alloc){
        list_remove(PRED_P_BLKP(bp));
        list_remove(SUCC_P_BLKP(bp));
        size += GET_SIZE(HDRP(PRED_P_BLKP(bp))) + GET_SIZE(FTRP(SUCC_P_BLKP(bp)));
        PUT(HDRP(PRED_P_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(SUCC_P_BLKP(bp)), PACK(size, 0));
        bp = PRED_P_BLKP(bp);
    }
    //새로운 블럭을 리스트에 넣는다.
    list_add(bp);
    return bp;
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size){
    void *oldptr = ptr;
    void *newptr;
    size_t copy_size;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copy_size = GET_SIZE(HDRP(oldptr));
    if (size < copy_size)
        copy_size = size;
    memcpy(newptr, oldptr, copy_size);
    mm_free(oldptr);
    return newptr;
} 