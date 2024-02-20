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
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// size
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x)>(y)? (x):(y))

//pack a size and allocated bit into a word
#define PACK(size,alloc) ((size)|(alloc))

//read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p)=(val))

//read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

//given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp))- DSIZE)

//given block ptr bp, compute address of nest and previous blocks
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp)-DSIZE)))

//explicit 
#define GET_PRED(bp) (*(void**)(bp))
#define GET_SUCC(bp) (*(void**)((char*)(bp+WSIZE)))

//segregated
#define SEGREGATED_SIZE 12
#define GET_ROOT(class) (*(void**)((char*)(heap_listp)+(WSIZE*class)))

static char *free_listp;
static char *heap_listp;

//사이즈 맞는 가용 리스트 찾는 함수
int get_class(size_t size){
    if (size < 16)
        return -1;
    
    size_t class_sizes[SEGREGATED_SIZE];
    class_sizes[0] = 16;

    for(int i = 0; i<SEGREGATED_SIZE;i++){
        if(i!=0)
            // 쉬프트 연산자: 왼쪽으로 한칸 이동=>2배 => 즉 class_sizes 값을 넣는 과정
            class_sizes[i] = class_sizes[i-1]<<1;
        if(size<=class_sizes[i])
            return i;
    }
    // 주어진 크기가 마지막 클래스 크기를 넘어간다면 마지막 클래스로    
    return SEGREGATED_SIZE -1;
}


static void splice_free_block(void* bp){
    ////////////////////explicit /////////////////////
    // if(bp == free_listp){
    //     free_listp = GET_SUCC(free_listp);
    //     return;
    // }
    // GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // if(GET_SUCC(bp)!= NULL)
    //     GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
    ////////////////////////////////////////////

    ////////////////////segregated///////////////////
    int class = get_class(GET_SIZE(HDRP(bp)));
    if(bp==GET_ROOT(class)){//만약 첫번째꺼 제거한다면 다음블록을 root로
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class));
        return;
    }
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp); //제거 블록의 next를 이전블록과 연결
    if(GET_SUCC(bp)!=NULL)//제거블록의 next가 있었다면 next의 pre를 이전블록과 연결
         GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}
static void add_free_block(void* bp){
    //////////////LIFO///////////////
    // GET_SUCC(bp) = free_listp;
    // if(free_listp!=NULL)
    //     GET_PRED(free_listp) = bp;
    // free_listp = bp;
    /////////////////////////////////

    /////////////주소정책/////////////
    // void *cur = free_listp;
    // if(cur == NULL){ //아무것도 없었던 상태
    //     free_listp = bp;
    //     GET_SUCC(bp) = NULL;
    //     return;
    // }
    // while(cur<bp){
    //     if(GET_SUCC(cur) == NULL || GET_SUCC(cur)>bp)
    //         break; 
    //     cur = GET_SUCC(cur);
    // }
    // GET_SUCC(bp) = GET_SUCC(cur);
    // GET_SUCC(cur) = bp;
    // GET_PRED(bp) = cur;
    // if(GET_SUCC(bp)!=NULL){
    //     GET_PRED(GET_SUCC(bp)) = bp;
    // }
    ////////////////////////////////////

    ///////segregated: 맨앞으로 추가/////////
    int class = get_class(GET_SIZE(HDRP(bp)));
    GET_SUCC(bp) = GET_ROOT(class);
    if(GET_ROOT(class)!=NULL)
        GET_PRED(GET_ROOT(class)) = bp;
    GET_ROOT(class) = bp;
    ////////////////////////////////////
}

static void *coalesce(void *bp){
    ////////////////////  implicit  /////////////////////
    // size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // size_t size = GET_SIZE(HDRP(bp));

    // //case 1
    // if(prev_alloc && next_alloc){
    //     return bp;
    // }
    // //case 2 
    // else if(prev_alloc && !next_alloc){
    //     size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
    //     PUT(HDRP(bp),PACK(size,0));
    //     PUT(FTRP(bp),PACK(size,0));
    // } 
    // //case 3
    // else if(!prev_alloc && next_alloc){
    //     size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
    //     PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
    //     PUT(FTRP(bp),PACK(size,0));
    //     bp = PREV_BLKP(bp);
    // }
    // //case 4
    // else{
    //     size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
    //     PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
    //     PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
    //     bp = PREV_BLKP(bp);
    // }
    // return bp;
    //////////////////////////////////////////////////////

    ////////////////////implicit - LIFO & segregated ///////////////////
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //case 1
    if(prev_alloc && next_alloc){
        add_free_block(bp);
        return bp;
    }
    //case 2 
    else if(prev_alloc && !next_alloc){
        splice_free_block(NEXT_BLKP(bp));
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    } 
    //case 3
    else if(!prev_alloc && next_alloc){
        splice_free_block(PREV_BLKP(bp));
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    //case 4
    else{
        splice_free_block(PREV_BLKP(bp));
        splice_free_block(NEXT_BLKP(bp));
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    add_free_block(bp);
    return bp;
    //////////////////////////////////////////////////////
    
    /////////////////explicit - 주소정책/////////////////
    // size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // size_t size = GET_SIZE(HDRP(bp));

    // //case 1
    // if(prev_alloc && next_alloc){
    //     add_free_block(bp);
    //     return bp;
    // }
    // //case 2 
    // else if(prev_alloc && !next_alloc){
    //     splice_free_block(NEXT_BLKP(bp));
    //     size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
    //     PUT(HDRP(bp),PACK(size,0));
    //     PUT(FTRP(bp),PACK(size,0));
    //     add_free_block(bp);
    // } 
    // //case 3
    // else if(!prev_alloc && next_alloc){
    //     size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
    //     PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
    //     PUT(FTRP(bp),PACK(size,0));
    //     bp = PREV_BLKP(bp);
    // }
    // //case 4
    // else{
    //     splice_free_block(NEXT_BLKP(bp));
    //     size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
    //     PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
    //     PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
    //     bp = PREV_BLKP(bp);
    // }
    // return bp;
    ////////////////////////////////////////////////////////////////
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    
    //allocate an even number of words to maintain alignment
    size = (words % 2)? (words+1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1) 
        return NULL;

    //Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    //Coalesce if the previous block was free 
    return coalesce(bp);
}
/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{   
    ///////////////////// implicit/////////////////////////
    // char *heap_listp;
    // // create the initial empty heap
    // if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1) 
    //     return -1;
    // PUT(heap_listp,0);
    // PUT(heap_listp + (1 * WSIZE),PACK(DSIZE,1));
    // PUT(heap_listp + (2 * WSIZE),PACK(DSIZE,1));
    // PUT(heap_listp + (3 * WSIZE),PACK(0,1));
    // heap_listp += 2 * WSIZE;

    // // extend the empty heap with a free block of CHUNKSIZE bytes
    // if(extend_heap(CHUNKSIZE/WSIZE) == NULL) 
    //     return -1;
    // return 0;
    /////////////////////////////////////////////////////////

    ///////////////////explicit//////////////////////////////
    // if((free_listp = mem_sbrk(8*WSIZE)) == (void*)-1) 
    //     return -1;
    // PUT(free_listp,0);//정렬패딩
    // PUT(free_listp + (1 * WSIZE),PACK(DSIZE,1));//프롤로그 헤더
    // PUT(free_listp + (2 * WSIZE),PACK(DSIZE,1));//프롤로그 푸터
    // PUT(free_listp + (3 * WSIZE),PACK(4*WSIZE,0));// 첫가용 블록 헤더
    // PUT(free_listp + (4 * WSIZE),NULL); //이전 가용 블록 주소
    // PUT(free_listp + (5 * WSIZE),NULL); //이후 가용 블록 주소
    // PUT(free_listp + (6 * WSIZE),PACK(4*WSIZE,0));//첫가용 블록 푸터
    // PUT(free_listp + (7 * WSIZE),PACK(0,1)); //에필로그
    // free_listp += 4 * WSIZE;//블록의 prev 가리키고 있음

    // // extend the empty heap with a free block of CHUNKSIZE bytes
    // if(extend_heap(CHUNKSIZE/WSIZE) == NULL) 
    //     return -1;
    // return 0;
    ////////////////////////////////////////////////////////////

    ////////////////////segregated//////////////////////////////
    if((heap_listp = mem_sbrk((SEGREGATED_SIZE+4)*WSIZE)) == (void*)-1) 
        return -1;
    PUT(heap_listp,0);
    PUT(heap_listp + (1 * WSIZE),PACK((SEGREGATED_SIZE+2)*WSIZE,1));// 프롤로그 헤더
    for(int i=0;i<SEGREGATED_SIZE;i++){
        PUT(heap_listp+((2+i)*WSIZE),NULL);
    }
    PUT(heap_listp + ((SEGREGATED_SIZE+2)* WSIZE),PACK((SEGREGATED_SIZE+2)*WSIZE,1));//프롤로그 푸터
    PUT(heap_listp + ((SEGREGATED_SIZE+3) * WSIZE),PACK(0,1));//에필로그
    heap_listp += 2 * WSIZE;

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
    ////////////////////////////////////////////////////////////
}
static void *find_fit(size_t asize){
    /////////////////first-fit : implicit ///////////////////////
    // void *bp = mem_heap_lo()+2*WSIZE;
    // while(GET_SIZE(HDRP(bp))>0){
    //     if(!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp)))) 
    //         return bp;
    //     bp = NEXT_BLKP(bp);
    // }
    /////////////////////////////////////////////////////////////

    //////////////////best-fit : implicit //////////////////////
    // void *bp = mem_heap_lo()+2*WSIZE;
    // void *best_fit = NULL;
    // void *min_bp = (void *)-1;//제일 큰 크기

    // while(GET_SIZE(HDRP(bp))>0){
    //     if(!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp)))){
    //         if(GET_SIZE(HDRP(bp))<min_bp){
    //             min_bp = GET_SIZE(HDRP(bp));
    //             best_fit = bp;
    //         }
    //     }
    //     bp = NEXT_BLKP(bp);
    // }
    // return best_fit;
    //////////////////////////////////////////////////

    //////////////explicit: first-fit/////////////////
    // void *bp = free_listp;
    // while(bp!=NULL){
    //     if(asize<=GET_SIZE(HDRP(bp)))
    //         return bp;
    //     bp = GET_SUCC(bp);
    // }
    // return NULL;
    ///////////////////////////////////////////////////

    /////////////////segregated////////////////////////
    int class = get_class(asize);
    void *bp = GET_ROOT(class);
    while(class<SEGREGATED_SIZE){
        bp = GET_ROOT(class);
        while(bp!=NULL){
            if(asize<=GET_SIZE(HDRP(bp)))
                return bp;
            bp = GET_SUCC(bp);
        }
        class += 1;
    }
    return NULL;
}

static void place(void *bp,size_t asize){
    /////////////implicit///////////////////
    // size_t csize = GET_SIZE(HDRP(bp));

    // if((csize - asize) >= (2*DSIZE)){
    //     PUT(HDRP(bp),PACK(asize,1));
    //     PUT(FTRP(bp),PACK(asize,1));

    //     PUT(HDRP(NEXT_BLKP(bp)),PACK(csize-asize,0));
    //     PUT(FTRP(NEXT_BLKP(bp)),PACK(csize-asize,0));
    // }else{
    //     PUT(HDRP(bp),PACK(csize,1));
    //     PUT(FTRP(bp),PACK(csize,1));
    // }
    ////////////////////////////////////////

    //////////////explicit: LIFO & segregated //////////////////
    splice_free_block(bp);
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));

        PUT(HDRP(NEXT_BLKP(bp)),PACK(csize-asize,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(csize-asize,0));
        add_free_block(NEXT_BLKP(bp));
    }else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
    ///////////////////////////////////////////////

    //////////////explicit:주소정책/////////////////
    // size_t csize = GET_SIZE(HDRP(bp));

    // if((csize - asize) >= (2*DSIZE)){
    //     PUT(HDRP(bp),PACK(asize,1));
    //     PUT(FTRP(bp),PACK(asize,1));
    //     bp = NEXT_BLKP(bp);
    //     PUT(HDRP(bp),PACK(csize-asize,0));
    //     PUT(FTRP(bp),PACK(csize-asize,0));

    //     GET_SUCC(bp)=GET_SUCC(PREV_BLKP(bp));

    //     if(PREV_BLKP(bp) == free_listp){
    //         free_listp = bp; //이미 할당 됐으니까 바꿔주자
    //     }else{
    //         GET_PRED(bp) = GET_PRED(PREV_BLKP(bp));
    //         GET_SUCC(GET_PRED(PREV_BLKP(bp))) = bp;
    //     }
 
    //     if(GET_SUCC(bp) != NULL){
    //         GET_PRED(GET_SUCC(bp)) = bp;
    //     }

    // }else{
    //     splice_free_block(bp);
    //     PUT(HDRP(bp),PACK(csize,1));
    //     PUT(FTRP(bp),PACK(csize,1));
    // }
    ////////////////////////////////////////////////
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    //ignore spurious requests
    if(size == 0) return NULL;

    //adjust block size to include overhead and alignment reqs
    if(size <= DSIZE) 
        asize = 2*DSIZE;
    else 
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE);

    //search the free list for a fit 
    if((bp = find_fit(asize)) !=NULL){
        place(bp,asize);
        return bp;
    }
    //no fit found. Get more memory and place the block
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE))==NULL) 
        return NULL;
    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if(ptr == NULL)
        return mm_malloc(size);
    if(size <= 0){
        mm_free(ptr);
        return 0;
    }
    void *newptr = mm_malloc(size);
    if(newptr == NULL) 
        return NULL;

    size_t copysize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if(size<copysize) 
        copysize = size;
    memcpy(newptr,ptr,copysize);
    mm_free(ptr);
    return newptr;
}














