/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing 
 * the brk pointer.  A block is pure payload. There are no headers or footers.
 * Blocks are never coalesced or reused. Realloc is implemented 
 * directly using mm_malloc and mm_free.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* declare mm_check as static */
//static int mm_check(void);
static  void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp,size_t asize);

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4

#define DSIZE 8

#define CHUNKSIZE (1<<12)

#define MAX(x,y)  ((x) > (y)? (x):(y))

#define PACK(size,alloc)  ((size) | (alloc))

#define OVERHEAD 8

#define GET(p)   (*(size_t *)(p))

#define PUT(p,val)   (*(size_t *)(p) =(val))

#define GET_SIZE(p)  (GET(p) & ~0x7)

#define GET_ALLOC(p)  (GET(p) & 0x1)

#define HDRP(bp)      ((char *)(bp)-WSIZE)

#define FTRP(bp)      ((char *)(bp)+GET_SIZE(HDRP(bp))-DSIZE)


#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))

#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))


void *heap_listp;
void *next = NULL;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp=mem_sbrk(4*WSIZE))==NULL)
    {
        return -1;
    }

    PUT(heap_listp,0);
    
    PUT(heap_listp+WSIZE,PACK(OVERHEAD,1));
    
    PUT(heap_listp+DSIZE,PACK(OVERHEAD,1));
    
    PUT(heap_listp+WSIZE+DSIZE,PACK(0,1));

    heap_listp += DSIZE;
    if(extend_heap(CHUNKSIZE/WSIZE)==NULL)
    {
        return -1;
    }
    next = heap_listp;
    
    return 0;	 
}

static  void *extend_heap(size_t words)
{
    void* bp;
    size_t size;

    size=(words%2) ? (words+1)*WSIZE:words*WSIZE;

    if((int)(bp=mem_sbrk(size))<0)
        return NULL;

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    return coalesce(bp);
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size=GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));

    coalesce(ptr);
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{

    void *oldptr=ptr;
    void *newptr;
    size_t oldsize;

    if(size < 0)
    {
        return NULL;
        
    }

    if(ptr == NULL)
    {
       return  mm_malloc(size); 
        
    }else if(size == 0)
    {
        mm_free(ptr);
        
        return NULL;
    }
    else 
    {
	
        oldsize=GET_SIZE(HDRP(ptr));
	
	//printf("the first : %c and the second : %c\n",*(char *)ptr,*(char *)((char *)ptr + WSIZE));
	//int temp1 = GET(ptr);
	//int temp2 = GET((char *)ptr + WSIZE);
	//int temp1=0,temp2=0;
	//memcpy(&temp1,oldptr,8);

	mm_free(oldptr);
        newptr = mm_malloc(size);
	
        size =  GET_SIZE(HDRP(newptr));
	//memcpy(newptr,oldptr,size);
	//memcpy(newptr,&temp1,8);
	//*(int *)newptr = temp1;
	//*((char *)newptr + WSIZE) = temp2;
	// printf("the first : %c and the second : %c\n",*(char *)newptr,*(char *)((char *)newptr + WSIZE));
        if (oldsize <size)
        {
            memcpy(newptr,oldptr,oldsize-DSIZE); 
            
        }else
        {
            
            memcpy(newptr,oldptr,size-DSIZE); 
	    }

	// mm_free(oldptr);

           return newptr;
        
    }
}

/*
 * mm_check - Does not currently check anything
 */
//static int mm_check(void)
//{
// printf("You have no hopes!"); 
// return 1;
//}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void  *bp;
    if(size<=0)
    {
        return NULL;
    }

    if(size <= DSIZE)
    {
        asize = DSIZE + OVERHEAD;
        
    }else
    {
        asize = DSIZE *((size +(OVERHEAD) + (DSIZE - 1))/DSIZE);
    }
    if((bp = find_fit(asize)) !=NULL)
    {
        place(bp,asize);

        return bp;
    }

    extendsize = MAX(asize,CHUNKSIZE);

    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
    {

        return NULL;
    }

    // mm_check();
    place(bp,asize);
    return bp;
}
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size       = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc)
    {
        return bp;
    }
    else if(prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));

        return bp;
    }
    else if(!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));

        return (void *)(PREV_BLKP(bp));
        
    }else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));

        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));

        return (void *)(PREV_BLKP(bp));
        
    }    
}

static void *find_fit(size_t asize)
{
    void *bp;
    //printf("heap_listp : %p\n",heap_listp);
    // printf("next : %p\n",next);
    
    for(bp=next;GET_SIZE(HDRP(bp))>0;bp = NEXT_BLKP(bp))
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
	    //printf("current bp: %p",bp);
	    return (void *)bp;
        }
        
    }
    next = heap_listp;
    return NULL;
}

static void place(void *bp,size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (DSIZE + OVERHEAD))
    {
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        bp=NEXT_BLKP(bp);

        PUT(HDRP(bp),PACK(csize - asize ,0));
        PUT(FTRP(bp),PACK(csize - asize ,0));
        
        
    }
    else
    {
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
    
    
}





