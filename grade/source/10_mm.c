#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

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


//对齐的单位
#define ALIGNMENT 8

//对大小为size的块进行对齐
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

//将size_t和指针对齐
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define PTR_SIZE (ALIGN(sizeof(void *)))

//定义最小的块的大小
#define MIN_BLK_SIZE (SIZE_T_SIZE*2 + PTR_SIZE*2)

/* Packs size and allocation bit, assuming proper alignment */
#define PACK(size, alloc) ((size) | (alloc))

//根据指针获得分配的块的其实地址
#define PAYLOADP(bp) ((void *)((char *)bp + SIZE_T_SIZE))
//根据内容获得指针
#define BLOCKP(pp) ((void *)((char *)pp - SIZE_T_SIZE))

//获得块的大小及是否分配
#define BLK_SIZE(bp) (HDR(bp) & ~0x3)
#define BLK_ALLOC(bp) (HDR(bp) & 0x3)

//获得块的header和footer
#define HDR(bp) (*((size_t *)bp))
#define FTR(bp) (*((size_t *)((char *)bp + BLK_SIZE(bp) - SIZE_T_SIZE)))

//获得空闲块的next和prev
#define NEXT(bp) (*((void **)((char *)bp + SIZE_T_SIZE)))
#define PREV(bp) (*((void **)((char *)bp + SIZE_T_SIZE + PTR_SIZE)))

//获得heap中的next和prev
#define LIN_NEXT(bp) ((void *)((char *)bp + BLK_SIZE(bp)))
#define LIN_PREV(bp) ((void *)((char *)bp - (*((size_t *)((char *)bp - SIZE_T_SIZE)) & ~0x3)))

//空闲块的信息(可以更改)
#define NUM_LISTS (128)
#define LIST_MAX_SIZE(n) (0x8*(1 << n))

#define ROOT(n) ((void *)((char *) mem_heap_lo() + SIZE_T_SIZE * n))

/*
 * 一些静态的操作
 */
static void *mm_append(size_t newsize, void *root);
static void *mm_findSpace(size_t newsize);
static void *mm_putTogether(void *ptr);
static void *mm_findFirBlo(size_t newsize, void *root);
static void mm_putList(void *ptr);
static void mm_insert(void *dest, void *blkp);
static void mm_remove(void *blkp);
static void mm_setBounds(void *blkp, size_t value);

/* 
 * mm_init - Initialize the malloc package
 *     Makes a root block that provides access to all the free lists in the heap.
 */
int mm_init(void)
{
	//生成的数组的大小
	size_t rootblocksize = MIN_BLK_SIZE+SIZE_T_SIZE*(NUM_LISTS-1);
	if(mem_sbrk(rootblocksize) == (void *)-1)
		return -1;
	int i;
	for(i = 0; i < NUM_LISTS; i++)
		NEXT(ROOT(i)) = NULL;
        mm_setBounds(mem_heap_lo(), PACK(rootblocksize, 0x2));
	return 0;
}

/*
 * mm_malloc - Returns a pointer to the payload of a block
 *     May split a larger free block for allocation. Relocates the tail free block.
 */
void *mm_malloc(size_t size)
{

	size_t newsize = ALIGN(size + SIZE_T_SIZE*2);
	if(newsize < MIN_BLK_SIZE)
		newsize = MIN_BLK_SIZE;
	
	void *found = mm_findSpace(newsize);

	if(found == NULL)
		return NULL;

	
	mm_remove(found);

	size_t tail_size = BLK_SIZE(found) - newsize;
	if(tail_size < MIN_BLK_SIZE)
    {
        
    mm_setBounds(found, PACK(BLK_SIZE(found), 0x1));
   //HDR(found) = PACK(BLK_SIZE(found),0x1);
   //FTR(found) = PACK(BLK_SIZE(found),0x1);
    }else
	{
		mm_setBounds(found, PACK(newsize, 0x1));
       //HDR(found) =  PACK(newsize, 0x1);
       //FTR(found) =  PACK(newsize, 0x1);
		void *tail = LIN_NEXT(found);
		mm_setBounds(tail, PACK(tail_size, 0x0));
		
      // HDR(tail) =  PACK(tail_size, 0x0);
       //FTR(tail) =  PACK(tail_size, 0x0);
		mm_putList(tail);
	}


	return PAYLOADP(found);
}

/*
 * mm_free - Mark a block as free then unfloat it.
 */
void mm_free(void *payload)
{


	void *blkp = BLOCKP(payload);
	mm_setBounds(blkp, PACK(BLK_SIZE(blkp), 0x0));

	blkp = mm_putTogether(blkp);

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	void *oldptr = ptr;
	void *newptr;
	size_t copySize;
	
	newptr = mm_malloc(size);
	if(newptr == NULL)
		return NULL;
	copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
	if(size < copySize)
		copySize = size;
	memcpy(newptr, oldptr, copySize);
	mm_free(oldptr);
	return newptr;
}

/*
 * 扩展大小
 */
static void *mm_append(size_t newsize, void *root)
{
	void *heaptail = LIN_PREV(mem_heap_hi()+1);
	void *found;

	if(BLK_ALLOC(heaptail) == 0x0)
	{
		size_t extension = newsize - BLK_SIZE(heaptail);
		found = mem_sbrk(extension);
		if (found == (void *)-1)
			return NULL;

		mm_setBounds(found, PACK(extension, 0x0));

		found = mm_putTogether(found);
	}
	else
	{
		void *extra = mem_sbrk(newsize);
		if (extra == (void *)-1)
			return NULL;

		mm_setBounds(extra, PACK(newsize, 0x0));
		mm_insert(root, extra);

		found = mem_sbrk(newsize);
		if (found == (void *)-1)
			return NULL;

		mm_setBounds(found, PACK(newsize, 0x0));
		mm_insert(root, found);
	}

	return found;
}

/*
 *找到一个合适范围的大小
 */
static void *mm_findSpace(size_t newsize)
{
	int i = 0;
	void *returnval = NULL;

	
	for(i; LIST_MAX_SIZE(i) <= newsize; i++);
    	int first = i;

	for(i; i < NUM_LISTS; i++)
	{
		if(NEXT(ROOT(i)) != NULL)
			returnval = mm_findFirBlo(newsize, ROOT(i));

		if (returnval != NULL)
			return returnval;	
	}

	return mm_append(newsize, ROOT(first));
}

/*
 * 合并空闲块
 */
static void *mm_putTogether(void *blkp)
{
	void *next = LIN_NEXT(blkp);
	void *prev = LIN_PREV(blkp);

	if(next < mem_heap_hi()+1 && BLK_ALLOC(next) == 0x0)
	{
		mm_remove(next);
		mm_setBounds(blkp, PACK(BLK_SIZE(blkp) + BLK_SIZE(next), 0x0));
	}
	if(BLK_ALLOC(prev) == 0x0)
	{
		mm_remove(prev);
		mm_setBounds(prev, PACK(BLK_SIZE(prev) + BLK_SIZE(blkp), 0x0));
		mm_putList(prev);
		return prev;
	}
	else
	{
		mm_putList(blkp);
		return blkp;
	}
}

/*
 * 找到空闲块的第一个返回
 */
static void *mm_findFirBlo(size_t newsize, void *root)
{
	void *blkp = NEXT(root);
	void *found = NULL;
	while(blkp != NULL && found == NULL)
	{
		if(BLK_SIZE(blkp) >= newsize)
			found = blkp;
		blkp = NEXT(blkp);
	}
	return found;
}

/*
 * 将空闲块放入合适范围的链表中
 */
static void mm_putList(void *ptr)
{
	int i = 0;
	for(i; LIST_MAX_SIZE(i) <= BLK_SIZE(ptr); i++);
    	mm_insert(ROOT(i), ptr);
}

/*
 * 将一个block插入到另一个block中
 */
static void mm_insert(void *dest, void *blkp)
{
/*	PREV(blkp) = dest;
	NEXT(blkp) = NEXT(dest);
	if(NEXT(dest) != NULL)
		PREV(NEXT(dest)) = blkp;
	NEXT(dest) = blkp;*/
    void* prev = dest;
    dest = NEXT(dest);
    while(dest!=NULL&&BLK_SIZE(blkp) > BLK_SIZE(dest))
    {
        prev = dest;
        dest = NEXT(dest);
    }
    if(dest == NULL)
    {
        NEXT(prev) = blkp;
        PREV(blkp) = prev;
        NEXT(blkp) = NULL;
        return;
    }
    NEXT(prev) = blkp;
    PREV(blkp) = prev;
    NEXT(blkp) = dest;
    PREV(dest) = blkp;
    return;
}

/*
 *将一个块从空闲块中删除
 */
static void mm_remove(void *blkp)
{
	NEXT(PREV(blkp)) = NEXT(blkp);
	if(NEXT(blkp) != NULL)
		PREV(NEXT(blkp)) = PREV(blkp);
}

/*
 * 设置一个块的header和footer
 */
static void mm_setBounds(void *blkp, size_t value)
{
	HDR(blkp) = value;
	FTR(blkp) = value;
}


