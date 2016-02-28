/*
 * mm.c - Malloc implementation using segregated fits with address-ordered
 *        explicit linked lists and reallocation heuristics
 *
 * Each block is wrapped in a 4-byte header and a 4-byte footer. Free blocks
 * are stored in one of many linked lists segregated by block size. The n-th
 * list contains blocks with a byte size that spans 2^n to 2^(n+1)-1. Within
 * each list, blocks are sorted by memory address in ascending order.
 * Coalescing is performed immediately after each heap extension and free
 * operation. Reallocation is performed in place, using a buffer and a
 * reallocation bit to ensure the availability of future block expansion.
 *
 * Header entries consist of the block size (all 32 bits), reallocation tag
 * (second-last bit), and allocation bit (last bit).
 *
 *
 * He (Henry) Tian
 * Section 3
 * 5/13/13
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*
 * Team identification
 */
team_t team = {
    "9",
    "zph",
    "swr",
    "whj"
};

/*
 * Constants and macros
 */
#define WSIZE     4       /* Word size in bytes */
#define DSIZE     8       /* Double word size in bytes */
#define CHUNKSIZE (1<<12) /* Page size in bytes */
#define MINSIZE   16      /* Minimum block size */

#define LISTS     20      /* Number of segregated lists */
#define BUFFER  (1<<7)    /* Reallocation buffer */

#define MAX(x, y) ((x) > (y) ? (x) : (y)) /* Maximum of two numbers */
#define MIN(x, y) ((x) < (y) ? (x) : (y)) /* Minimum of two numbers */

/* Pack size and allocation bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)            (*(unsigned int *)(p))
// Preserve reallocation bit
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))
// Clear reallocation bit
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

/* Store predecessor or successor pointer for free blocks */
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

/* Adjust the reallocation tag */
#define SET_TAG(p)   (*(unsigned int *)(p) = GET(p) | 0x2)
#define UNSET_TAG(p) (*(unsigned int *)(p) = GET(p) & ~0x2)

/* Read the size and allocation bit from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p)   (GET(p) & 0x2)

/* Address of block's header and footer */
#define HEAD(ptr) ((char *)(ptr) - WSIZE)
#define FOOT(ptr) ((char *)(ptr) + GET_SIZE(HEAD(ptr)) - DSIZE)

/* Address of next and previous blocks */
#define NEXT(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

/* Address of free block's predecessor and successor entries */
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

/* Address of free block's predecessor and successor on the segregated list */
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))

/* Check for alignment */
#define ALIGN(p) (((size_t)(p) + 7) & ~(0x7))

/* Settings for mm_check */
#define CHECK         0 /* Kill bit: Set to 0 to disable checking
                           (Checking is currently disabled through comments) */
#define CHECK_MALLOC  1 /* Check allocation operations */
#define CHECK_FREE    1 /* Check free operations */
#define CHECK_REALLOC 1 /* Check reallocation operations */
#define DISPLAY_BLOCK 1 /* Describe blocks in heap after each check */
#define DISPLAY_LIST  1 /* Describe free blocks in lists after each check */
#define PAUSE         1 /* Pause after each check, also enables the function to
                           skip displaying mm_check messages*/
                           
#define LINE_OFFSET   4 /* Line offset for referencing trace files */

/*
 * Global variables
 */
void *free_lists[LISTS]; /* Array of pointers to segregated free lists */
char *prologue_block;    /* Pointer to prologue block */

/* Variables for checking function 
int line_count; // Running count of operations performed
int skip;       // Number of operations to skip displaying mm_check messages
                // (Checking still occurs)
*/

/*
 * Function prototypes
 */
static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

//static void mm_check(char caller, void *ptr, int size);

/* 
 * mm_init - Initialize the malloc package. Construct prologue and epilogue
 *           blocks.
 */
int mm_init(void)
{
  int list;         // List counter
  char *heap_start; // Pointer to beginning of heap
  
  /* Initialize array of pointers to segregated free lists */
  for (list = 0; list < LISTS; list++) {
    free_lists[list] = NULL;
  }

  /* Allocate memory for the initial empty heap */
  if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
    return -1;
  
  PUT_NOTAG(heap_start, 0);                            /* Alignment padding */
  PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
  prologue_block = heap_start + DSIZE;
  
  /* Extend the empty heap */
  if (extend_heap(CHUNKSIZE) == NULL)
    return -1;
    
  /* Variables for checking function
  line_count = LINE_OFFSET;
  skip = 0;
  */
  
  return 0;
}

/* 
 * mm_malloc - Allocate a new block by placing it in a free block, extending
 *             heap if necessary. Blocks are padded with boundary tags and
 *             lengths are changed to conform with alignment.
 */
void *mm_malloc(size_t size)
{
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  void *ptr = NULL;  /* Pointer */
  int list = 0;      /* List counter */
  
  /*
  size_t checksize = size; // Copy of request size
                           // (Reported to checking function)
  */
  
  /* Filter invalid block size */
  if (size == 0)
    return NULL;
  
  /* Adjust block size to include boundary tags and alignment requirements */
  if (size <= DSIZE) {
    asize = 2 * DSIZE;
  } else {
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }
  
  /* Select a free block of sufficient size from segregated list */
  size = asize;
  while (list < LISTS) {
    if ((list == LISTS - 1) || ((size <= 1) && (free_lists[list] != NULL))) {
      ptr = free_lists[list];
      // Ignore blocks that are too small or marked with the reallocation bit
      while ((ptr != NULL)
        && ((asize > GET_SIZE(HEAD(ptr))) || (GET_TAG(HEAD(ptr)))))
      {
        ptr = PRED(ptr);
      }
      if (ptr != NULL)
        break;
    }
    
    size >>= 1;
    list++;
  }
  
  /* Extend the heap if no free blocks of sufficient size are found */
  if (ptr == NULL) {
    extendsize = MAX(asize, CHUNKSIZE);
    if ((ptr = extend_heap(extendsize)) == NULL)
      return NULL;
  }
  
  /* Place the block */
  place(ptr, asize);
  
  /*
  // Check heap for consistency
  line_count++;
  if (CHECK && CHECK_MALLOC) {
    mm_check('a', ptr, checksize);
  }
  */
  
  /* Return pointer to newly allocated block */
  return ptr;
}

/*
 * mm_free - Free a block by adding it to the appropriate list and coalescing
 *           it.
 */
void mm_free(void *ptr)
{
  size_t size = GET_SIZE(HEAD(ptr)); /* Size of block */
  
  /* Unset the reallocation tag on the next block */
  UNSET_TAG(HEAD(NEXT(ptr)));
  
  /* Adjust the allocation status in boundary tags */
  PUT(HEAD(ptr), PACK(size, 0));
  PUT(FOOT(ptr), PACK(size, 0));
  
  /* Insert new block into appropriate list */
  insert_node(ptr, size);
  
  /* Coalesce free block */
  coalesce(ptr);
  
  /*
  // Check heap for consistency
  line_count++;
  if (CHECK && CHECK_FREE) {
    mm_check('f', ptr, size);
  }
  */
  
  
  return;
}

/*
 * mm_realloc - Reallocate a block in place, extending the heap if necessary.
 *              The new block is padded with a buffer to guarantee that the
 *              next reallocation can be done without extending the heap,
 *              assuming that the block is expanded by a constant number of bytes
 *              per reallocation.
 *
 *              If the buffer is not large enough for the next reallocation, 
 *              mark the next block with the reallocation tag. Free blocks
 *              marked with this tag cannot be used for allocation or
 *              coalescing. The tag is cleared when the marked block is
 *              consumed by reallocation, when the heap is extended, or when
 *              the reallocated block is freed.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */
	
	/* Filter invalid block size */
  if (size == 0)
    return NULL;
  
  /* Adjust block size to include boundary tag and alignment requirements */
  if (new_size <= DSIZE) {
    new_size = 2 * DSIZE;
  } else {
    new_size = DSIZE * ((new_size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }
  
  /* Add overhead requirements to block size */
  new_size += BUFFER;
  
  /* Calculate block buffer */
  block_buffer = GET_SIZE(HEAD(ptr)) - new_size;
  
  /* Allocate more space if overhead falls below the minimum */
  if (block_buffer < 0) {
    /* Check if next block is a free block or the epilogue block */
    if (!GET_ALLOC(HEAD(NEXT(ptr))) || !GET_SIZE(HEAD(NEXT(ptr)))) {
      remainder = GET_SIZE(HEAD(ptr)) + GET_SIZE(HEAD(NEXT(ptr))) - new_size;
      if (remainder < 0) {
        extendsize = MAX(-remainder, CHUNKSIZE);
        if (extend_heap(extendsize) == NULL)
          return NULL;
        remainder += extendsize;
      }
      
      delete_node(NEXT(ptr));
      
      // Do not split block
      PUT_NOTAG(HEAD(ptr), PACK(new_size + remainder, 1)); /* Block header */
      PUT_NOTAG(FOOT(ptr), PACK(new_size + remainder, 1)); /* Block footer */
    } else {
      new_ptr = mm_malloc(new_size - DSIZE);
      //line_count--;
      memmove(new_ptr, ptr, MIN(size, new_size));
      mm_free(ptr);
      //line_count--;
    }
    block_buffer = GET_SIZE(HEAD(new_ptr)) - new_size;
  }  

  /* Tag the next block if block overhead drops below twice the overhead */
  if (block_buffer < 2 * BUFFER)
    SET_TAG(HEAD(NEXT(new_ptr)));

  /*
  // Check heap for consistency
  line_count++;
  if (CHECK && CHECK_REALLOC) {
    mm_check('r', ptr, size);
  }
  */
  
  /* Return reallocated block */
  return new_ptr;
}

/*
 * extend_heap - Extend the heap with a system call. Insert the newly
 *               requested free block into the appropriate list.
 */
static void *extend_heap(size_t size)
{
  void *ptr;                   /* Pointer to newly allocated memory */
  size_t words = size / WSIZE; /* Size of extension in words */
  size_t asize;                /* Adjusted size */
  
  /* Allocate an even number of words to maintain alignment */
  asize = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  
  /* Extend the heap */
  if ((long)(ptr = mem_sbrk(asize)) == -1)
    return NULL;
  
  /* Set headers and footer */
  PUT_NOTAG(HEAD(ptr), PACK(asize, 0));   /* Free block header */
  PUT_NOTAG(FOOT(ptr), PACK(asize, 0));   /* Free block footer */
  PUT_NOTAG(HEAD(NEXT(ptr)), PACK(0, 1)); /* Epilogue header */
  
  /* Insert new block into appropriate list */
  insert_node(ptr, asize);
  
  /* Coalesce if the previous block was free */
  return coalesce(ptr);
}

/*
 * insert_node - Insert a block pointer into a segregated list. Lists are
 *               segregated by byte size, with the n-th list spanning byte
 *               sizes 2^n to 2^(n+1)-1. Each individual list is sorted by
 *               pointer address in ascending order.
 */
static void insert_node(void *ptr, size_t size) {
  int list = 0;
  void *search_ptr = ptr;
  void *insert_ptr = NULL;
  
  /* Select segregated list */
  while ((list < LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }
  
  /* Select location on list to insert pointer while keeping list
     organized by byte size in ascending order. */
  search_ptr = free_lists[list];
  while ((search_ptr != NULL) && (size > GET_SIZE(HEAD(search_ptr)))) {
    insert_ptr = search_ptr;
    search_ptr = PRED(search_ptr);
  }
  
  /* Set predecessor and successor */
  if (search_ptr != NULL) {
    if (insert_ptr != NULL) {
      SET_PTR(PRED_PTR(ptr), search_ptr); 
      SET_PTR(SUCC_PTR(search_ptr), ptr);
      SET_PTR(SUCC_PTR(ptr), insert_ptr);
      SET_PTR(PRED_PTR(insert_ptr), ptr);
    } else {
      SET_PTR(PRED_PTR(ptr), search_ptr); 
      SET_PTR(SUCC_PTR(search_ptr), ptr);
      SET_PTR(SUCC_PTR(ptr), NULL);
      
      /* Add block to appropriate list */
      free_lists[list] = ptr;
    }
  } else {
    if (insert_ptr != NULL) {
      SET_PTR(PRED_PTR(ptr), NULL);
      SET_PTR(SUCC_PTR(ptr), insert_ptr);
      SET_PTR(PRED_PTR(insert_ptr), ptr);
    } else {
      SET_PTR(PRED_PTR(ptr), NULL);
      SET_PTR(SUCC_PTR(ptr), NULL);
      
      /* Add block to appropriate list */
      free_lists[list] = ptr;
    }
  }

  return;
}

/*
 * delete_node: Remove a free block pointer from a segregated list. If
 *              necessary, adjust pointers in predecessor and successor blocks
 *              or reset the list head.
 */
static void delete_node(void *ptr) {
  int list = 0;
  size_t size = GET_SIZE(HEAD(ptr));
  
  /* Select segregated list */
  while ((list < LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }
  
  if (PRED(ptr) != NULL) {
    if (SUCC(ptr) != NULL) {
      SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
      SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
    } else {
      SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
      free_lists[list] = PRED(ptr);
    }
  } else {
    if (SUCC(ptr) != NULL) {
      SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
    } else {
      free_lists[list] = NULL;
    }
  }
  
  return;
}

/*
 * coalesce - Coalesce adjacent free blocks. Sort the new free block into the
 *            appropriate list.
 */
static void *coalesce(void *ptr)
{
  size_t prev_alloc = GET_ALLOC(HEAD(PREV(ptr)));
  size_t next_alloc = GET_ALLOC(HEAD(NEXT(ptr)));
  size_t size = GET_SIZE(HEAD(ptr));
  
  /* Return if previous and next blocks are allocated */
  if (prev_alloc && next_alloc) {
    return ptr;
  }
  
  /* Do not coalesce with previous block if it is tagged */
  if (GET_TAG(HEAD(PREV(ptr))))
    prev_alloc = 1;
  
  /* Remove old block from list */
  delete_node(ptr);
  
  /* Detect free blocks and merge, if possible */
  if (prev_alloc && !next_alloc) {
    delete_node(NEXT(ptr));
    size += GET_SIZE(HEAD(NEXT(ptr)));
    PUT(HEAD(ptr), PACK(size, 0));
    PUT(FOOT(ptr), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) {
    delete_node(PREV(ptr));
    size += GET_SIZE(HEAD(PREV(ptr)));
    PUT(FOOT(ptr), PACK(size, 0));
    PUT(HEAD(PREV(ptr)), PACK(size, 0));
    ptr = PREV(ptr);
  } else {
    delete_node(PREV(ptr));
    delete_node(NEXT(ptr));
    size += GET_SIZE(HEAD(PREV(ptr))) + GET_SIZE(HEAD(NEXT(ptr)));
    PUT(HEAD(PREV(ptr)), PACK(size, 0));
    PUT(FOOT(NEXT(ptr)), PACK(size, 0));
    ptr = PREV(ptr);
  }
  
  /* Adjust segregated linked lists */
  insert_node(ptr, size);
  
  return ptr;
}

/*
 * place - Set headers and footers for newly allocated blocks. Split blocks
 *         if enough space is remaining.
 */
static void place(void *ptr, size_t asize)
{
  size_t ptr_size = GET_SIZE(HEAD(ptr));
  size_t remainder = ptr_size - asize;
  
  /* Remove block from list */
  delete_node(ptr);
  
  if (remainder >= MINSIZE) {
    /* Split block */
    PUT(HEAD(ptr), PACK(asize, 1)); /* Block header */
    PUT(FOOT(ptr), PACK(asize, 1)); /* Block footer */
    PUT_NOTAG(HEAD(NEXT(ptr)), PACK(remainder, 0)); /* Next header */
    PUT_NOTAG(FOOT(NEXT(ptr)), PACK(remainder, 0)); /* Next footer */  
    insert_node(NEXT(ptr), remainder);
  } else {
    /* Do not split block */
    PUT(HEAD(ptr), PACK(ptr_size, 1)); /* Block header */
    PUT(FOOT(ptr), PACK(ptr_size, 1)); /* Block footer */
  }
  return;
}

/*
 * mm_check - Heap consistency checker. Displays information on current
 *            memory operation. Prints information on all blocks and free list
 *            entries. Checks header and footer for consistency, as well as whether
 *            a free block is positioned in the correct list.
 *
 *            Can be set to pause, waiting for user input between checks. If
 *            pausing is enabled, also allows user to skip a number of checks.
 *
void mm_check(char caller, void* caller_ptr, int caller_size)
{
  int size;  // Size of block
  int alloc; // Allocation bit
  char *ptr = prologue_block + DSIZE;
  int block_count = 1;
  int count_size;
  int count_list;
  int loc;   // Location of block relative to first block
  int caller_loc = (char *)caller_ptr - ptr;
  int list;
  char *scan_ptr;
  char skip_input;
  
  if (!skip)
    printf("\n[%d] %c %d %d: Checking heap...\n",
      line_count, caller, caller_size, caller_loc);
  
  while (1) {
    loc = ptr - prologue_block - DSIZE;
    
    size = GET_SIZE(HEAD(ptr));
    if (size == 0)
      break;
    
    alloc = GET_ALLOC(HEAD(ptr));
    
    // Print block information
    if (DISPLAY_BLOCK && !skip) {
      printf("%d: Block at location %d has size %d and allocation %d\n",
        block_count, loc, size, alloc);
      if (GET_TAG(HEAD(ptr))) {
        printf("%d: Block at location %d is tagged\n",
          block_count, loc);
      }
    }
    
    // Check consistency of size and allocation in header and footer
    if (size != GET_SIZE(FOOT(ptr))) {
      printf("%d: Header size of %d does not match footer size of %d\n",
        block_count, size, GET_SIZE(FOOT(ptr)));
    }
    if (alloc != GET_ALLOC(FOOT(ptr))) {
      printf("%d: Header allocation of %d does not match footer allocation "
        "of %d\n", block_count, alloc, GET_ALLOC(FOOT(ptr)));
    }
    
    // Check if free block is in the appropriate list
    if (!alloc) {
      // Select segregated list
      list = 0;
      count_size = size;
      while ((list < LISTS - 1) && (count_size > 1)) {
        count_size >>= 1;
        list++;
      }
      
      // Check list for free block
      scan_ptr = free_lists[list];
      while ((scan_ptr != NULL) && (scan_ptr != ptr)) {
        scan_ptr = PRED(scan_ptr);
      }
      if (scan_ptr == NULL) {
        printf("%d: Free block of size %d is not in list index %d\n",
          block_count, size, list);
      }
    }
    
    ptr = NEXT(ptr);
    block_count++;
  }
  
  if (!skip)
    printf("[%d] %c %d %d: Checking lists...\n",
      line_count, caller, caller_size, caller_loc);
  
  // Check every list of free blocks for validity
  for (list = 0; list < LISTS; list++) {
    ptr = free_lists[list];
    block_count = 1;
    
    while (ptr != NULL) {
      loc = ptr - prologue_block - DSIZE;
      size = GET_SIZE(HEAD(ptr));
      
      // Print free block information
      if (DISPLAY_LIST && !skip) {
        printf("%d %d: Free block at location %d has size %d\n",
          list, block_count, loc, size);
        if (GET_TAG(HEAD(ptr))) {
          printf("%d %d: Block at location %d is tagged\n",
            list, block_count, loc);
        }
      }
      
      // Check if free block is in the appropriate list
      count_list = 0;
      count_size = size;
      
      while ((count_list < LISTS - 1) && (count_size > 1)) {
        count_size >>= 1;
        count_list++;
      }
      if (list != count_list) {
        printf("%d: Free block of size %d is in list %d instead of %d\n",
          loc, size, list, count_list);
      }
      
      // Check validity of allocation bit in header and footer
      if (GET_ALLOC(HEAD(ptr)) != 0) {
        printf("%d: Free block has an invalid header allocation of %d\n",
          loc, GET_ALLOC(FOOT(ptr)));
      }
      if (GET_ALLOC(FOOT(ptr)) != 0) {
        printf("%d: Free block has an invalid footer allocation of %d\n",
          loc, GET_ALLOC(FOOT(ptr)));
      }
      
      ptr = PRED(ptr);
      block_count++;
    }
  }
  
  if (!skip)
    printf("[%d] %c %d %d: Finished check\n\n",
      line_count, caller, caller_size, caller_loc);
  
  // Pause and skip function, toggled by PAUSE preprocessor directive. Skip
  // allows checker to stop pausing and printing for a number of operations.
  // However, scans are still completed and errors will still be printed.
  if (PAUSE && !skip) {
    printf("Enter number of operations to skip or press <ENTER> to continue.\n");
    
    while ((skip_input = getchar()) != '\n') {
      if ((skip_input >= '0') && (skip_input <= '9')) {
        skip = skip * 10 + (skip_input - '0');
      }
    }
    
    if (skip)
      printf("Skipping %d operations...\n", skip);
      
  } else if (PAUSE && skip) {
    skip--;
  }
  
  return;
}
*/
