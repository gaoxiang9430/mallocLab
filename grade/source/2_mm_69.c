/* 
 * Simple allocator based on implicit free lists with boundary 
 * tag coalescing. Each block has header and footer of the form:
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
#include <stdio.h>
#include "mm.h"
#include "memlib.h"

//team_t team = {"jepsin11mdemali","James Espinosa", "jespin11","Matt Demali","mdemali"}; /* so we're compatible with 15213 driver */
#define NEXT_FITx
team_t team = {
 #ifdef NEXT_FIT
   "2" ,                                                    //"implicit next fit", 
 #else
   "2",                                                  // "implicit first fit", 
 #endif
   "wang","song",                                             // "lmh", "lq",
      "chen"                                                           //"zzch"
}; 


/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)   /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Additional constants and macros */
#define PADDING    4
#define PROLOGSIZE 16
#define EPILOGSIZE 8
#define RIGHT(bp) ((void *)* (int *)(bp+WSIZE))
#define LEFT(bp) ((void *)* (int *)(bp))
#define SETLEFT(bp, bq) (*(int *)(bp)) = (int)(bq)
#define ADJUSTSIZE(size) ((((size) + DSIZE + 7) / DSIZE ) * DSIZE)
#define SETRIGHT(bp, bq) (*(int *)(bp+WSIZE)) = (int)(bq)
#define GETSIZE(bp) ((*(int*) (bp-WSIZE)) & ~7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  //store val where p is pointing to

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* The only global variable is a pointer to the first block */
static char *heap_listp;
static void *tree_root;

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* Additional function declarations */
void *mm_insert(void *root, void *bp);
void *mm_remove(void *root, void *bp);
void *mm_ceiling(void *root,  int size);
void *mm_parent(void *root, void *bp);
void *mm_replace(void *bp);
void *mm_remove_node(void *root, void *bp);
void *mm_remove_child(void *root, void *bp);
void *mm_remove_children(void *root, void *bp);

int mm_children(void *root);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    void *bp;

    tree_root = NULL;

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(PROLOGSIZE)) == NULL)
        return -1;

    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    bp = extend_heap(CHUNKSIZE/WSIZE);

    if (bp == NULL)
        return -1;

    tree_root = mm_insert(tree_root, bp);

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
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    
    /* Search the free list for a fit */
    if ((bp = mm_ceiling(tree_root,asize)) != NULL) 
    {
        tree_root = mm_remove(tree_root,bp);
        bp = place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);

    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    bp = place(bp, asize);

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

    tree_root = mm_insert(tree_root,coalesce(bp));
}

/* $end mmfree */

/* Not implemented. For consistency with 15-213 malloc driver */
void *mm_realloc(void *ptr, size_t size)
{   

    void *bp;
    size_t asize = ADJUSTSIZE(size);

    if(!GETSIZE(NEXT_BLKP(ptr)))
    {
        size_t extendsize = MAX(asize, CHUNKSIZE);
        bp = extend_heap(extendsize/4);
        size_t nsize = extendsize + GETSIZE(ptr) - asize;
        
        PUT(HDRP(ptr), PACK(asize,1));
        PUT(FTRP(ptr), PACK(asize,1));

        void *blk = NEXT_BLKP(ptr);
        PUT(HDRP(blk), PACK(nsize,0));
        PUT(FTRP(blk), PACK(nsize, 0));
        tree_root = mm_insert(tree_root, blk);
        
        return ptr;     
    }
    
    if(!(GET_ALLOC(HDRP(NEXT_BLKP(ptr)))))
    {
        bp = NEXT_BLKP(ptr);
        
        size_t total = GETSIZE(ptr) + GETSIZE(bp);

        if(total >= asize)
        {
            size_t nsize = total - asize;
            tree_root = mm_remove(tree_root,bp);
            
            if(nsize < 16)
            {
                PUT(HDRP(ptr), PACK(total, 1));
                PUT(FTRP(ptr), PACK(total, 1));
                return ptr;
            }
            else 
            {
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));
                
                void *blk = NEXT_BLKP(ptr);
                PUT(HDRP(blk), PACK(nsize,0));
                PUT(FTRP(blk), PACK(nsize,0));
                tree_root = mm_insert(tree_root, blk);
                
                return ptr;
            }                                    
        }

        else if(!GETSIZE(NEXT_BLKP(bp)))
        {
            size_t extendsize = MAX(asize, CHUNKSIZE);
            extend_heap(extendsize/4);
            size_t nsize = extendsize + total - asize;
            
            PUT(HDRP(ptr), PACK(asize,1));
            PUT(FTRP(ptr), PACK(asize,1));

            void *blk = NEXT_BLKP(ptr);
            PUT(HDRP(blk), PACK(nsize,0));
            PUT(FTRP(blk), PACK(nsize,0));
            tree_root = mm_insert(tree_root, blk);
            return ptr;
        }
    }
    
    bp = mm_malloc(size);
    
    memcpy(bp, ptr, (GETSIZE(ptr) - DSIZE));
    mm_free(ptr);
    return bp;  
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose) {
        printf("Heap (%p):\n", heap_listp);
        printf("Root (%p):\n", tree_root);
    }

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
    if ((int)(bp = mem_sbrk(size)) == -1) 
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
static void *place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t split_size = (csize - asize);

    if (split_size >= (DSIZE + OVERHEAD)) {
        size_t avg = (GETSIZE(NEXT_BLKP(bp)) + GETSIZE(PREV_BLKP(bp)))/2; 
        void* large;
        void* small;
        int split_side;

        /* Which side should we split on? Let split_side = 0 or 1
           0 = Let's split the end
           1 = Let's split the front 
        */
        
        if(GETSIZE(NEXT_BLKP(bp)) > GETSIZE(PREV_BLKP(bp)))
        {
            large = NEXT_BLKP(bp);
            small = PREV_BLKP(bp);
        }
        else
        {
            large = PREV_BLKP(bp);
            small = NEXT_BLKP(bp);
        }
         
        if(asize > avg)
        {
            if(PREV_BLKP(bp) == large)
                split_side = 0;
            else 
                split_side = 1;           
        }
        else
        {
            if(PREV_BLKP(bp) == large)
                split_side = 1;
            else 
                split_side = 0;
        }
        
        if(split_side != 1)
        {
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));

            void* split = NEXT_BLKP(bp);

            PUT(HDRP(split), PACK(csize-asize, 0));
            PUT(FTRP(split), PACK(csize-asize, 0));

            tree_root = mm_insert(tree_root,split);

            return bp;
        }
        else
        {
            PUT(HDRP(bp), PACK(split_size,0));
            PUT(FTRP(bp), PACK(split_size,0));
        
            void *blk = NEXT_BLKP(bp);

            PUT(HDRP(blk), PACK(asize, 1));
            PUT(FTRP(blk), PACK(asize, 1));

            tree_root = mm_insert(tree_root,bp);

            return blk;
        }
    }
    else
    { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        return bp;
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */


static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
    void *bp;

    /* first fit search */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* no fit */
}
/* $end mmfirstfit */

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
/* $begin mmfree */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1: Neighbors both allocated */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2: Only the previous is allocated*/
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        /* If only the previous block is allocated, remove the next block */
        tree_root = mm_remove(tree_root, NEXT_BLKP(bp));

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));

        return(bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3: Only the next is allocated */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        /* If only the next block is allocated, remove the previous block */
        tree_root = mm_remove(tree_root, PREV_BLKP(bp));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        return(PREV_BLKP(bp));
    }

    else {                                     /* Case 4: Neither are allocated */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));

        /* If neither blocks are allocated, remove them both */
        tree_root = mm_remove(tree_root, NEXT_BLKP(bp));
        tree_root = mm_remove(tree_root, PREV_BLKP(bp));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        return(PREV_BLKP(bp));
    }
}
/* $end mmfree */

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

    if (bp == heap_listp) {
      printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, hsize, (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f')); 

    } else if (!halloc) {
      printf("%p: header: [%d:%c] | left: %p, right: %p | footer: [%d:%c]\n", bp, hsize, (halloc ? 'a' : 'f'),
         LEFT(bp), RIGHT(bp), fsize, (falloc ? 'a' : 'f')); 

    } else {
      printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, hsize, (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f')); 
    }
  
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
 * mm_insert - Insert a free block into the Binary Tree and return bp
 */
void *mm_insert(void *root, void* bp)
{
    /* Determine if the tree is empty and initiate all nodes to NULL */

    if(root == NULL)
    {
        SETLEFT(bp, NULL);
        SETRIGHT(bp, NULL);
        return bp;
    }

    else if(GETSIZE(bp) <= GETSIZE(root))
    {
        SETLEFT(root, mm_insert(LEFT(root),bp));
        return root;
    }

    else if(GETSIZE(bp) >  GETSIZE(root))
    {
        SETRIGHT(root, mm_insert(RIGHT(root),bp));
        return root;
    }
    
    /* If there's an error, return -1 */
    return (void*)-1;
}

/*
 * mm_remove - Remove a node from the Binary Tree
 */
void *mm_remove(void *root, void *bp)
{
    /* Determine if there are any children, if not, remove the node */

    if(mm_children(bp) == 0)
        return mm_remove_node(root, bp);

    else if(mm_children(bp) == 1)
        return mm_remove_child(root, bp);

    else
        return mm_remove_children(root, bp);
}

/*
 * mm_ceiling - Locate a node that best fits in a free block and return its pointer
 */
void * mm_ceiling(void* root, int size)
{
    void* best_fit;

    /* Retrieve the best fit, check its size and determine if it works */
    
    if(root == NULL)
        return NULL;
        
    int root_size = GETSIZE(root);
    
    if(root_size  ==  size)
        return root;

    else if(root_size > size)
        best_fit = mm_ceiling(LEFT(root), size);

    else if (root_size < size)
        best_fit = mm_ceiling(RIGHT(root), size);

    /* Determine size of child and see if the node is a good fit */
    if(best_fit == NULL)
    {
        if(root_size < size) /* If it's too small, return NULL */
            return NULL;
        else 
            return root;
    }
    else 
        return best_fit;
                    
}


/*
 * mm_parent - Retrieve the parent node of a child node
 */
void *mm_parent(void *root, void *bp)
{
    if(bp == root)
        return NULL;

    if(GETSIZE(bp) <= GETSIZE(root))
    {
        if(LEFT(root) == bp)
            return root;
        else
            return mm_parent(LEFT(root),bp);
    }
    else
    {
        if(RIGHT(root) == bp)
            return root;
        else
            return mm_parent(RIGHT(root),bp);
    }
} 

/*
 * mm_children - Return the number of children under a given root node
 */
int mm_children(void *root)
{
    int child_num = 0;

    /* Do we have any children on either side? */

    if(LEFT(root) != NULL)
         child_num++;
    if(RIGHT(root) != NULL)
         child_num++;
                            
    return child_num;
}         

/*
 * mm_remove_node - If a given node has no children, lets remove it.
 */
void *mm_remove_node(void *root, void *bp)
{
    void *parent_node = mm_parent(root, bp);
    
    if(parent_node != NULL)
    {
        if(LEFT(parent_node) == bp) 
            SETLEFT(parent_node, NULL);
        else 
            SETRIGHT(parent_node, NULL);
        return root;
    } 
    else
    {
        return NULL;
    }
}

/*
 * mm_remove_child - Remove the node from the Binary Tree as long as it has one child
 */
void *mm_remove_child(void *root, void* bp)
{
    void *parent_node = mm_parent(root, bp);
    void *child;
    
    /* Who is our child? Where is it? */

    if(LEFT(bp) != NULL)
        child = LEFT(bp);
    else
        child = RIGHT(bp);

    if(parent_node != NULL)
    {
        if(LEFT(parent_node) == bp)
            SETLEFT(parent_node, child);
        else 
            SETRIGHT(parent_node, child); 
        return root;
    }
    else
    {
        return child;                               
    }
}

/*
 * mm_remove_children - Remove the node from the Binary Tree as long as it has two children
 */
void *mm_remove_children(void *root, void *bp)
{
    void *parent_node = mm_parent(root, bp);
    void *replacement = mm_replace(LEFT(bp));
    void *new_bp;
    
    /* Remove the replacement and store the new bp */

    new_bp = mm_remove(LEFT(bp), replacement);
    
    SETLEFT(replacement, new_bp);
    SETRIGHT(replacement, RIGHT(bp));
    
    if(parent_node != NULL) 
    {
        if(LEFT(parent_node) == bp)
            SETLEFT(parent_node, replacement);
        else
            SETRIGHT(parent_node, replacement);
        return root;
    }
    else
    {
        return replacement; 
    }
}

/*
 * mm_replace - Locate the replacement for the parents' two children
 */
void *mm_replace(void *bp)
{
     if(RIGHT(bp) == NULL)
        return bp;
     else
        return mm_replace(RIGHT(bp));
}
