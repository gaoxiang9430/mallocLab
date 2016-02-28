/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */


#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
//#define NEXT_FITx

/* Team structure */
team_t team = {
#ifdef NEXT_FIT
    "3", 
#else
    "3", 
#endif
    "swc", "sbp",
    "wf"
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))      

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))	//得到地址ｐ的数据
#define PUT(p, val)  (*(size_t *)(p) = (val))  	//将地址ｐ中放入ｖａｌ

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)	//消掉低三位
#define GET_ALLOC(p) (GET(p) & 0x1)	//直留最低位

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  //得到上一个字的地址
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)//得到最后一个字的地址

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))//得到下一个块地址
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))//
/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
#ifdef NEXT_FIT
static char *rover;       /* next fit rover */
#endif

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);


//added
#define SC_SIZE 1030
#define SC_FACT_SIZE 1027
#define NODE_SIZE 1000000
#define LISTS 20
struct node{
	void *bp;
	struct node* next;
};
struct node* sc[LISTS];
struct node active[NODE_SIZE];
int n_index=0;
void gen(void* bp){
	size_t size=GET_SIZE(HDRP(bp));
	int list=0;
	while(size>1&&list<LISTS-1){
		size>>=1;	
		list++;
	}
	struct node* a;
	//a=(struct node*)malloc(sizeof(struct node));
	a=&active[n_index++];
	(*a).bp=bp;
	(*a).next=sc[list];
	sc[list]=a;
}
void del(void* bp){
	size_t size=GET_SIZE(HDRP(bp));
	int list=0;
	while(size>1&&list<LISTS-1){
		size>>=1;	
		list++;
	}
	struct node* fit=sc[list];
	struct node* prev=NULL;
	while(fit!=0){
		if((*fit).bp==bp){
			if(prev==NULL)
				sc[list]=(*fit).next;
			else{
				(*prev).next=(*fit).next;
			}
			return;
		}
		prev=fit;
		fit=(*fit).next;
	}
}



//added finish
/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */

int mm_init(void) 
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;

	void* ap;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if ((ap=extend_heap(CHUNKSIZE/WSIZE)) == NULL)
	return -1;
	int i;
	for(i=0;i<LISTS;i++){
		sc[i]=0;
	}
	size_t sz=GET_SIZE(HDRP(ap));
	struct node *a;
	//a=(struct node*)malloc(sizeof(struct node));
	a=&active[n_index++];
	int list=0;
	int sz_f=sz;
	while(sz_f>1&&list<LISTS-1){
		sz_f>>=1;
		list++;
	}
	(*a).bp=ap,(*a).next=0;
	sc[list]=a;
	
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	asize = DSIZE + OVERHEAD;
    else
	asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);//巧妙的上取整算法
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
	place(bp, asize);
	return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
	return NULL;
    del(bp);
    place(bp, asize);
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
	printf("ERROR: mm_malloc failed in mm_realloc\n");
	exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
	printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    }
     
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   
	//查看放入之后是否还可以再防置
    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
	gen(bp);
    }
    else { 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
 static void *find_fit(size_t asize){
 	struct node* fit;
 	struct node* prev;
	int list=0;
	int sz_f=asize;
	while(sz_f>1&&list<LISTS-1){
		sz_f>>=1;
		list++;
	}
 	int i;
 	for(i=list;i<LISTS;i++){
 		fit=sc[i];
 		int j=0;
	 	while(fit!=0&&GET_SIZE(HDRP((*fit).bp) )<asize ){
	 		prev=fit;
	 		fit=(*fit).next;
	 		j++;
	 	}
	 	if(fit!=0){
	 		//要删除
	 		if(j==0)
	 			sc[i]=(*fit).next;
	 		else
	 			(*prev).next=(*fit).next;
	 		return (*fit).bp;
	 	}
 	}
 	return NULL;


 }
 
// static void *find_fit(size_t asize)
// {
// #ifdef NEXT_FIT 
//     /* next fit search */
//     char *oldrover = rover;

//     /* search from the rover to the end of list */
//     for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
// 	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
// 	    return rover;

//     /* search from start of list to old rover */
//     for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
// 	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
// 	    return rover;

//     return NULL;  /* no fit found */
// #else 
//     /* first fit search */
//     void *bp;

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
// 	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
// 	    return bp;
// 	}
//     }
//     return NULL; /* no fit */
// #endif
// }

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
    
    gen(bp);

	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
    del(NEXT_BLKP(bp));
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));
	gen(bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
    del(PREV_BLKP(bp));
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
	gen(bp);
    }

    else {                                     /* Case 4 */
    del(PREV_BLKP(bp));
    del(NEXT_BLKP(bp));
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
	gen(bp);
    }
    return bp;
}


static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
	   hsize, (halloc ? 'a' : 'f'), 
	   fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}

