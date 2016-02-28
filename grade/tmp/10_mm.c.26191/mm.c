
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
#ifdef NEXT_FIT
    //"implicit next fit", 
    "team10",
#else
    //"implicit first fit", 
    "team10",
#endif
    "pangbin", "gaojing",
    "wangwenjian"
}; 

/* Block headers. */
typedef struct header_t {
	size_t data;
	struct header_t *next;
	struct header_t *prev;
} header_t;

static header_t *free_listp;

header_t *find_fit(size_t size);
void coalesce(header_t *header);
void remove_block_from_free_list(header_t *header);
void push_onto_free_list(header_t *header);
void extend_heap(size_t size);


#define ALIGNMENT 8

//#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define ALIGN(size) ALIGNMENT*((size+(ALIGNMENT)+(ALIGNMENT-1))/ALIGNMENT);

#define HEADER_SIZE (ALIGN(sizeof(header_t)))

//#define DEFAULT_ALLOC_SIZE 32768

#define DEFAULT_ALLOC_SIZE 4096

#define DEFAULT_ALLOC_SIZE512 512


inline static void* get_alloc(header_t *header) {
	return (void*) ((char*)header + HEADER_SIZE);
}


inline static header_t* get_header(void *ptr) {
	return (header_t*) ((char*)ptr - HEADER_SIZE);
}


inline static size_t is_allocated(header_t *header) {
	return (header->data & 0x1);
}

inline static unsigned int is_in_bounds(header_t *header) {
	return (header == NULL) ? 0 : ((unsigned int)header >= (unsigned int)mem_heap_lo()) && ((unsigned int)header <= (unsigned int)mem_heap_hi());
}


inline static size_t get_size(header_t *header) {
	return (header->data & ~0x7);
}


inline static void set_header(header_t *header, size_t size, size_t allocated) {
	header->data = (size | allocated);
}

inline static header_t* next_block(header_t *header) {
	return (header_t *)((char *)header + get_size(header) + 2*HEADER_SIZE);
}


inline static header_t* prev_block(header_t *header) {
	header_t *prev_block_footer = (header_t *)((char *)header - HEADER_SIZE);
	return is_in_bounds(prev_block_footer) ? (header_t *)((char *)header - get_size(prev_block_footer) - 2*HEADER_SIZE) : NULL;
}


inline static header_t* get_footer(header_t *header) {
	return (header_t *)((char *)header + get_size(header) + HEADER_SIZE);
}


int mm_init(void) {
	free_listp = NULL;
    return 0;
}

void *mm_malloc(size_t size) {	
	size = (size <= 212) ? 212 : size;
	
	
	
	header_t *header = find_fit(size);
	
	if (header == NULL) {
		extend_heap(size);
		header = find_fit(size);
	}

	size_t current_size = get_size(header);
	size_t aligned_size = ALIGN(size);
	if ((current_size - aligned_size) >= 4*HEADER_SIZE) {
		set_header(header, aligned_size, 1);
		set_header(get_footer(header), aligned_size, 1);
		header_t *next_block_header = next_block(header);
		set_header(next_block_header, current_size - aligned_size - 2*HEADER_SIZE, 0);
		set_header(get_footer(next_block_header), current_size - aligned_size - 2*HEADER_SIZE, 0);
		push_onto_free_list(next_block_header);
	} else {
		set_header(header, current_size, 1);
		set_header(get_footer(header), current_size, 1);
	}
	
	if (header == free_listp) {
		free_listp = free_listp->next;
		if (is_in_bounds(free_listp)) {
			free_listp->prev = NULL;
		}
	} else if (!is_in_bounds(header->next)) {
		header->prev->next = NULL;
		header->prev = NULL;
	} else {
		header->next->prev = header->prev;
		header->prev->next = header->next;
	}

	return get_alloc(header);
}

void mm_free(void *ptr) {
	header_t *header = get_header(ptr);
	size_t esize = get_size(header);
	
	set_header(header, esize, 0);
	set_header(get_footer(header), esize, 0);
	coalesce(header);
}


void *mm_realloc(void *ptr, size_t size) {
	if (ptr == NULL) {
		return mm_malloc(size);
	}
	
	if (size <= 0) {
		mm_free(ptr);
		return NULL;
	}
	
	void *oldptr = ptr;
	void *newptr = oldptr;
	
	header_t *old_header = get_header(oldptr);
	header_t *next_block_header;
	header_t *prev_block_header;
	
	size_t aligned_size = ALIGN(size);
	size_t block_size = get_size(old_header);
	
	if (block_size < aligned_size) {
		size_t newsize = block_size;
		next_block_header = next_block(old_header);
		prev_block_header = prev_block(old_header);
		
		if (is_in_bounds(prev_block_header) && !is_allocated(prev_block_header)) {
			newsize += get_size(prev_block_header) + 2*HEADER_SIZE;
			newptr = get_alloc(prev_block_header);
		}
		
		if (newsize >= aligned_size) {
			remove_block_from_free_list(prev_block_header);
			set_header(get_header(newptr), newsize, 1);
			set_header(get_footer(get_header(newptr)), newsize, 1);
			memcpy(newptr, oldptr, block_size);
		} else {
			if (is_in_bounds(next_block_header) && !is_allocated(next_block_header)) {
				newsize += get_size(next_block_header) + 2*HEADER_SIZE;
			}
			
			if (newsize >= aligned_size) {
				remove_block_from_free_list(next_block_header);
				set_header(get_header(newptr), newsize, 1);
				set_header(get_footer(get_header(newptr)), newsize, 1);
			} else {
				newptr = mm_malloc(aligned_size);
				memcpy(newptr, oldptr, block_size);
				mm_free(oldptr);
			}
		}

		return newptr;
	} else {
		return newptr;
	}
}


header_t *find_fit(size_t size) {
	header_t *header = free_listp;
	
	while (is_in_bounds(header)) {
		if (!is_allocated(header) && size <= get_size(header)) {
			return header;
		}
		header = header->next;
	}
	
	return NULL;
}


void coalesce(header_t *header) {
	header_t *next_block_header = next_block(header);
	header_t *prev_block_header = prev_block(header);
		
	if (is_in_bounds(next_block_header) && !is_allocated(next_block_header)) {
		remove_block_from_free_list(next_block_header);
		size_t newsize = get_size(header) + get_size(next_block_header) + 2*HEADER_SIZE;
		set_header(header, newsize, 0);
		set_header(get_footer(next_block_header), newsize, 0);
	}
	
	if (is_in_bounds(prev_block_header) && !is_allocated(prev_block_header)) {
		remove_block_from_free_list(prev_block_header);
		size_t newsize = get_size(prev_block_header) + get_size(header) + 2*HEADER_SIZE;
		set_header(get_footer(header), newsize, 0);
		set_header(prev_block_header, newsize, 0);
		push_onto_free_list(prev_block_header);
		return;
	}
	
	push_onto_free_list(header);
}


void remove_block_from_free_list(header_t *header) {
	header_t *next_block_header = header->next;
	header_t *prev_block_header = header->prev;
	
	if (!is_in_bounds(prev_block_header) && !is_in_bounds(next_block_header)) {
		free_listp = NULL;
	} else if (!is_in_bounds(prev_block_header) && is_in_bounds(next_block_header)) {
		free_listp = free_listp->next;
		free_listp->prev = NULL;
	} else if (is_in_bounds(prev_block_header) && !is_in_bounds(next_block_header)) {
		prev_block_header->next = NULL;
	} else {
		prev_block_header->next = next_block_header;
		next_block_header->prev = prev_block_header;
	}
}


void push_onto_free_list(header_t *header) {
	header_t *current_header = free_listp;
	
	if (is_in_bounds(current_header)) {
		current_header->prev = header;
	}
	header->next = current_header;
	header->prev = NULL;
	free_listp = header;
}


void extend_heap(size_t size) {
	void *p;
	size_t alloc_size;
	if (size <= (DEFAULT_ALLOC_SIZE512 - 2*HEADER_SIZE)) {
		alloc_size = DEFAULT_ALLOC_SIZE512;
	} else if (size <= (DEFAULT_ALLOC_SIZE - 2*HEADER_SIZE)) {
		alloc_size = DEFAULT_ALLOC_SIZE;
	} else {
		alloc_size = ALIGN(size + 2*HEADER_SIZE);
	}
	p = mem_sbrk(alloc_size);
	if (p == (void *)-1) {
		return;
	} else {
	    header_t *header = (header_t *)p;
		size_t esize = alloc_size - 2*HEADER_SIZE;
		header->next = NULL;
		header->prev = NULL;
	
		set_header(header, esize, 0);
		set_header(get_footer(header), esize, 0);
	
		push_onto_free_list(header);
	}
}
