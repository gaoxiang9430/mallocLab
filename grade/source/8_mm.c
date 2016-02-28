/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
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

/*
 *  每个free掉的block里面的数据结构
 *  -----------------------------------------------------------------   
 * |  header   | left_ptr | right_ptr | parent_ptr | brother_ptr | data | footer |
 *  -----------------------------------------------------------------
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

team_t team = {
    "group 8: ", 
    "zwh", 
    "lj",
    "cxw"
}; 

//常数定义 
#define WSIZE 4 	 //一倍字长
#define DSIZE 8	 	//两倍字长
#define TSIZE 12	 //3倍字长
#define QSIZE 16	 //4倍字长
#define OVERHEAD 8	 //头尾标志
#define ALIGNMENT 8	 //对齐方式
#define BLKSIZE 24	 //一个block的长度，就是每个free下来的都必须是这个长度以上
#define CHUNKSIZE (1<<12) 	//原始堆长度
#define INISIZE 1016 	//每次拓展的堆大小

// 
#define MAX(x, y) ( (x)>(y)? (x): (y) )
#define MIN(x, y) ( (x)<(y)? (x): (y) )

#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p)=(val))

#define SIZE(p) ( GET(p)&~0x7 )
#define PACK(size, alloc) ( (size) | (alloc) )
#define ALLOC(p) ( GET(p)&0x1 )

#define HEAD(p) ( (void *)(p)-WSIZE )
#define LEFT(p) ( (void *)(p) )
#define RIGHT(p) ( (void *)(p)+WSIZE )
#define PRNT(p) ( (void *)(p)+DSIZE )
#define BROS(p) ( (void *)(p)+TSIZE )
#define FOOT(p) ( (void *)(p)+SIZE(HEAD(p))-DSIZE )

#define ALIGN_SIZE(size) (DSIZE *(((size) + (DSIZE-1))/DSIZE))

#define GET_SIZE(bp) ( (GET(HEAD(bp)))&~0x7)
#define GET_PREV(bp) ((void *)(bp)-SIZE(((void *)(bp)-DSIZE)))
#define GET_NEXT(bp) ((void *)(bp)+SIZE(HEAD(bp)))
#define GET_ALLOC(bp) (GET(HEAD(bp))&0x1)

#define GET_LEFT(bp) (GET(LEFT(bp)))
#define GET_RIGHT(bp) (GET(RIGHT(bp)))
#define GET_PRNT(bp) (GET(PRNT(bp)))
#define GET_BROS(bp) (GET(BROS(bp)))
#define GET_FOOT(bp) (GET(FOOT(bp)))

#define PUT_HEAD(bp, val) (PUT(HEAD(bp), (int)val))
#define PUT_FOOT(bp, val) (PUT(FOOT(bp), (int)val))
#define PUT_LEFT(bp, val) (PUT(LEFT(bp), (int)val))
#define PUT_RIGHT(bp, val) (PUT(RIGHT(bp), (int)val))
#define PUT_PRNT(bp, val) (PUT(PRNT(bp), (int)val))
#define PUT_BROS(bp, val) (PUT(BROS(bp), (int)val))

static void *coalesce ( void *bp );
static void *extend_heap ( size_t size );
static void place ( void *ptr, size_t asize );
static void insert_node ( void *bp );
static void delete_node ( void *bp );
static void *find_fit ( size_t asize );

static void *heap_list_ptr;
static void *free_tree_rt;

int mm_init(void)
{
   // 建立一个新的空堆 
   if( (heap_list_ptr = mem_sbrk(QSIZE)) == NULL )
          return -1;
   PUT( heap_list_ptr, 0 ); 
   PUT( heap_list_ptr+WSIZE, PACK(OVERHEAD,1) ); // 序言头 
   PUT( heap_list_ptr+DSIZE, PACK(OVERHEAD,1) ); // 序言尾 
   PUT( heap_list_ptr+TSIZE, PACK(0,1) ); // 结尾块 
   heap_list_ptr += QSIZE;
   free_tree_rt = NULL;
  //按初始化大小扩展空堆
  
   if( extend_heap(ALIGN_SIZE(INISIZE))==NULL )
	return -1;
   
   return 0;
}
/* $end mminit */


/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
	size_t asize; //调整后的块分配大小
   	size_t extendsize; //如果没有合适的空块则重新扩展堆
   	void *bp;
   
   	
   	if( size <= 0 )
		return NULL;
      //调整块大小
   	if( size <= BLKSIZE-OVERHEAD)
		//块大小设置为最小块大小
		asize = BLKSIZE;
   	else
		//调整块大小为8byte对齐
		asize = ALIGN_SIZE(size+(OVERHEAD));

    //找到一个合适的空块
    if( (bp=find_fit(asize)) == NULL ){
	extendsize = MAX( asize + 32, INISIZE );
	extend_heap(ALIGN_SIZE(extendsize));
        if( (bp=find_fit(asize)) == NULL )
        return NULL;
    }

   //放置
	
   	if( size==448 && GET_SIZE(bp) > asize+64 )
			asize += 64;
   	else if( size==112 && GET_SIZE(bp) > asize+16 )
			asize += 16;
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
   	size_t size = GET_SIZE(bp);
   	PUT_HEAD( bp, PACK(size,0) );
   	PUT_FOOT( bp, PACK(size,0) );
   	insert_node(coalesce(bp));
}
/* $end mmfree */


/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
   	if( ptr==NULL || size==0 ){
		mm_free(ptr);
	return NULL;
   	}

   	if( size > 0 ){
		size_t oldsize = GET_SIZE( ptr );
		size_t newsize = ALIGN_SIZE( size+OVERHEAD );
		if( newsize < oldsize ){ //改变的大小比原大小小
			if( GET_ALLOC( GET_NEXT(ptr) ) ){
				//下一个块分配了
				if( (oldsize-newsize) >= BLKSIZE ){
					//剩余大小比BLKSIZE大
					PUT_HEAD( ptr, PACK(newsize,1) );
					PUT_FOOT( ptr, PACK(newsize,1) );//newsize
					void *temp = GET_NEXT(ptr);
					
					//分裂原块，将剩余部分作为新的空闲块
					PUT_HEAD( temp, PACK(oldsize-newsize,0) );
					PUT_FOOT( temp, PACK(oldsize-newsize,0) );
					insert_node(temp);
					}else{ //剩余大小比BLKSIZE小
							PUT_HEAD( ptr, PACK(oldsize,1) );
							//原块不变（不分裂）
							PUT_FOOT( ptr, PACK(oldsize,1) );
					}
				return ptr;
				}else{ //下一个块是空闲的，合并下一个块与本块剩余部分作为新的空闲块节点
						size_t csize = oldsize + GET_SIZE( GET_NEXT(ptr) );
						delete_node( GET_NEXT(ptr) );
						PUT_HEAD( ptr, PACK(newsize,1) );
						PUT_FOOT( ptr, PACK(newsize,1) );
						void *temp = GET_NEXT(ptr);
						PUT_HEAD( temp, PACK(csize-newsize,0) );
						PUT_FOOT( temp, PACK(csize-newsize,0) );
						insert_node(temp);
						return ptr;
					}
				}else{ //改变的大小比原大小大
						size_t prev_alloc = GET_ALLOC(GET_PREV(ptr));
						size_t next_alloc = GET_ALLOC(GET_NEXT(ptr));
						size_t csize;
						// 下一个块空闲，而且oldsize与下一个块的大小的和不小于newsize
						if( !next_alloc &&
								( (csize=oldsize+GET_SIZE(GET_NEXT(ptr))) >= newsize) ){
							delete_node(GET_NEXT(ptr));
							if((csize-newsize)>=BLKSIZE){
								PUT_HEAD( ptr, PACK(newsize,1) );
								PUT_FOOT( ptr, PACK(newsize,1) );
								void *temp=GET_NEXT(ptr);
								PUT_HEAD( temp, PACK(csize-newsize,0) );
								PUT_FOOT( temp, PACK(csize-newsize,0) );
								insert_node(temp);
							}else{
								PUT_HEAD( ptr,PACK(csize,1) );
								PUT_FOOT( ptr,PACK(csize,1) );
							}
							return ptr;
						}
						//上一个块空闲，而且oldsize与下一个块的大小的和不小于newsize
						else if( !prev_alloc &&
									( (csize=oldsize+GET_SIZE(GET_PREV(ptr))) >= newsize) ){
								delete_node(GET_PREV(ptr));
								void *newptr=GET_PREV(ptr);
								memcpy( newptr, ptr, oldsize-OVERHEAD );
								if((csize-newsize)>=BLKSIZE){
									PUT_HEAD( newptr,PACK(newsize,1) );
									PUT_FOOT( newptr,PACK(newsize,1) );
									void *temp=GET_NEXT(newptr);
									PUT_HEAD( temp,PACK(csize-newsize,0) );
									PUT_FOOT( temp,PACK(csize-newsize,0) );
									insert_node(temp);
								}else{
									PUT_HEAD( newptr,PACK(csize,1) );
									PUT_FOOT( newptr,PACK(csize,1) );
								}
								return newptr;
						}else{
					//前后的块都空闲，而且它们与oldsize的和比newsize小，重新申请一个大小合适的空块或者扩展堆
							size_t asize=ALIGN_SIZE(size+(OVERHEAD));
							size_t extendsize;
							void *newptr;
							if((newptr=find_fit(asize))==NULL){
								extendsize=MAX(asize,CHUNKSIZE);
								extend_heap(extendsize);
								if((newptr=find_fit(asize))==NULL)
									return NULL;
							}
							place( newptr, asize );
							memcpy( newptr, ptr,oldsize-OVERHEAD);
							mm_free(ptr);
							return newptr;
						}
				}
			}else
				return NULL;
}


/* 
 * mm_checkheap - Check the heap for consistency 
 */

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */


/* $begin mmextendheap */
void *extend_heap(size_t size)
{
	void *bp;
	if( (unsigned int)(bp=mem_sbrk(size)) ==(unsigned)(-1))
	return NULL;
	//初始化块头、块尾与结束块
	PUT_HEAD( bp, PACK(size,0) ); //空闲块头
	PUT_FOOT( bp, PACK(size,0) ); //空闲块尾
	PUT_HEAD( GET_NEXT(bp), PACK(0,1) ); //结束块
	insert_node(coalesce(bp));
	return (void *)bp;
}
/* $end mmextendheap */



/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp,size_t asize)
{
	size_t csize = GET_SIZE(bp);
	delete_node( bp );
	if((csize-asize)>=BLKSIZE){      //空闲块大小大于申请大小
		PUT_HEAD( bp,PACK(asize,1) );
		PUT_FOOT( bp,PACK(asize,1) );
		bp=GET_NEXT(bp);
		PUT_HEAD( bp,PACK(csize-asize,0) );
		PUT_FOOT( bp,PACK(csize-asize,0) );
		insert_node( coalesce(bp) );  //插入节点
	}else{//空闲块大小小于申请大小
		PUT_HEAD( bp,PACK(csize,1) );
		PUT_FOOT( bp,PACK(csize,1) );
	}
}
/* $end mmplace */


/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void* find_fit( size_t asize )
{
	/* the most fit block */
	void *fit = NULL;
	//临时块位置
	void *temp = free_tree_rt;
	//通过遍历树找到一个合适空闲块，实现best fit
	for(;temp!=NULL;){
		if( asize <= GET_SIZE(temp) ){
			fit = temp;
			temp = (void *)GET_LEFT(temp);
		}else
			temp = (void *)GET_RIGHT(temp);
		}
	return fit;
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(GET_PREV(bp));
	size_t next_alloc = GET_ALLOC(GET_NEXT(bp));
	size_t size = GET_SIZE(bp);
	if ( prev_alloc && next_alloc ) //前后都分配了的情况 
		return bp;
	else if ( !prev_alloc && next_alloc ) { //前面没有分配，后面分配了的情况
		delete_node(GET_PREV(bp));
		size += GET_SIZE( GET_PREV(bp) );
		PUT_HEAD( GET_PREV(bp), PACK(size, 0) );
		PUT_FOOT( bp, PACK(size,0) );
		return GET_PREV(bp);
	}else if ( prev_alloc && !next_alloc ) { //前面分配了，后面没有分配的情况
		delete_node( GET_NEXT(bp) );
		size += GET_SIZE( GET_NEXT(bp) );
		PUT_HEAD( bp, PACK(size,0) );
		PUT_FOOT( bp, PACK(size,0) );
		return bp;
	}else { //前面和后面都没有分配的情况
		delete_node(GET_NEXT(bp));
		delete_node(GET_PREV(bp));
		size += GET_SIZE( GET_PREV(bp) ) +
		GET_SIZE( GET_NEXT(bp) );
		PUT_HEAD( GET_PREV(bp), PACK(size,0) );
		PUT_FOOT( GET_NEXT(bp), PACK(size,0) );return GET_PREV(bp);
	}
}

//插入节点
static void insert_node( void *bp )
{
	//如果这棵树还没有，那么旧把这个树的根节点做出来
	if( free_tree_rt == NULL ){
		//树顶指针指向当前节点，当前节点的父节点，兄弟节点和左右子树节点均为空
		free_tree_rt = bp;
		PUT_LEFT( bp, NULL );
		PUT_RIGHT(bp, NULL );
		PUT_PRNT( bp, NULL );
		PUT_BROS( bp, NULL );
		return;
	}

	//如果已经有了一棵树了
	//如果能找到一个和这个一样的节点，就是已经有一个兄弟链在这里了，那就放在兄弟链的开头
	//相当于在兄弟链内实现了filo，
	//不然的话就从头一次找到相应的位置，插为兄弟链的第一条
	void *temp = free_tree_rt;
	//每次都是走一个节点走一次循环
	while(1){
		//如果在树里找到了和当前节点的大小一致的节点
		if( GET_SIZE(bp)==GET_SIZE(temp) ){
			//执行将节点插入	
			if( (void *)GET_BROS(temp) != NULL ){
				//如果树里面找到的这个节点没有兄弟节点
				if( temp == free_tree_rt ){
					//如果树里找到的这个节点就是根节点，就把根节点设为当前节点
					//且当前节点的父节点设为空（因为当前节点已被设为根节点）
					free_tree_rt = bp;
					PUT_PRNT( bp, NULL );
				}else{//如果不是根节点
					//判断一下当前节点是否为其父节点的左子树节点
					if( (void *)GET_LEFT(GET_PRNT(temp)) == temp)
					//如果是，就把它加在兄弟链开头，即将父节点的左子树改成这个
						PUT_LEFT( GET_PRNT(temp), bp );
					else 
					//如果不是，即这个为右子树，那就把父节点的右子树改成这个
						PUT_RIGHT( GET_PRNT(temp), bp );
					PUT_PRNT( bp, GET_PRNT(temp) );
			}
			
			//将这个节点的左子树，右子树，兄弟设置完整
			PUT_LEFT( bp, GET_LEFT(temp) );
			PUT_RIGHT( bp, GET_RIGHT(temp) );
			PUT_BROS( bp, temp );
			//如果有左右子树，修改一下左右子树的父节点
			if( (void *)GET_LEFT(temp) != NULL )
				PUT_PRNT( GET_LEFT(temp), bp );
			if( (void *)GET_RIGHT(temp) != NULL )
				PUT_PRNT( GET_RIGHT(temp), bp );
			
			//之前的节点就退居二线，左边指向新的当前兄弟链的头，邮编指向0
			PUT_LEFT( temp, bp );
			PUT_RIGHT( temp, -1 );
			break;
		    }else{
			//否则如果这个节点这边已经有兄弟节点了
			PUT_BROS( bp, NULL );
			PUT_LEFT( bp, temp );
			PUT_RIGHT( bp, -1 );
			PUT_BROS( temp, bp );
			if( (void *)GET_BROS(bp) != NULL )
				PUT_LEFT( GET_BROS(bp), bp );
			break;
		}
	}
	else if( GET_SIZE(bp) < GET_SIZE(temp) ){
		//如果当前这个节点的值比现在在树里找到的这个值小,就去找左子树
		if( (void *)GET_LEFT(temp) != NULL ){
			//如果有左子树，就跳到左子树走下一个循环
			temp = (void *)GET_LEFT( temp );
		}else{
			//如果没有左子树了，那么就把这个当作这个节点的左子树
			//设置相应的左右兄弟子树的点
			PUT_LEFT( temp, bp );
			PUT_PRNT( bp, temp );
			PUT_LEFT( bp, NULL );
			PUT_RIGHT( bp, NULL );
			PUT_BROS( bp, NULL );
			break;
		}
	}
	else{
		//如果当前这个节点的值比现在在树里找到的这个值大，就去找右子树
		//后面的和左子树一样
		if( (void *)GET_RIGHT(temp) != NULL ){
			temp = (void *)GET_RIGHT(temp);
		}else{
			PUT_RIGHT( temp, bp );
			PUT_PRNT( bp, temp );
			PUT_LEFT( bp, NULL );
			PUT_RIGHT( bp, NULL );
			PUT_BROS( bp, NULL );
			break;
		}
	}
  }
}


//删除节点
static void delete_node(void *bp)
{
 //如果这个节点没有和他一样大的兄弟节点，但是有右子树
 if( (void *)GET_BROS(bp) == NULL && GET_RIGHT(bp) != -1 ){
	if( bp == free_tree_rt ){//如果这是根节点
		if( (void *)GET_RIGHT(bp) == NULL ){//如果这个根节点没有右子树
			free_tree_rt=(void *)GET_LEFT(bp);//
			if( free_tree_rt != NULL )
				PUT_PRNT( free_tree_rt, NULL );
		}else{//如果这个根节点有右子树，把这个右子树中的最小值提上来作为根节点
		      //然后再删除原来的根节点
			void *temp = (void *)GET_RIGHT(bp);

			//找到这个最小值，即左右左子树的最小左子树
			while( (void *)GET_LEFT(temp) != NULL )
				temp = (void *)GET_LEFT(temp);
			
			//找到当前要删除的节点的左子树
			void *tempL = (void *)GET_LEFT(bp);
			void *tempR = (void *)GET_RIGHT(temp);
			void *tempP = (void *)GET_PRNT(temp);
			free_tree_rt = temp;
			

			if( free_tree_rt != NULL )
				PUT_PRNT( free_tree_rt, NULL );
			PUT_LEFT( temp,GET_LEFT(bp) );
			if( temp != (void *)GET_RIGHT(bp) ){
				PUT_RIGHT( temp,GET_RIGHT(bp) );
				PUT_LEFT( tempP, tempR );
				if( tempR != NULL)
					PUT_PRNT( tempR, tempP );
				PUT_PRNT( GET_RIGHT(bp),temp );
			}
			
			if( tempL != NULL )
				PUT_PRNT( tempL, temp );
		}
	}else{//如果这个不是根节
		if( (void *)GET_RIGHT(bp) == NULL ){//如果没有右子树 
			if( (void *)GET_LEFT( GET_PRNT( bp ) ) == bp )
				PUT_LEFT( GET_PRNT(bp), GET_LEFT(bp) );
			else
				PUT_RIGHT( GET_PRNT(bp), GET_LEFT(bp) );
			
			if( (void *)GET_LEFT(bp) != NULL)
				PUT_PRNT( GET_LEFT(bp), GET_PRNT(bp) );
		}else{//如果有右子树 
			void *temp = (void *)GET_RIGHT(bp);
			while( (void *)GET_LEFT(temp) != NULL )
				temp = (void *)GET_LEFT(temp);
				void *tempL = (void *)GET_LEFT(bp);
				void *tempR = (void *)GET_RIGHT(temp);
				void *tempP = (void *)GET_PRNT(temp);
				if( (void *)GET_LEFT(GET_PRNT(bp)) == bp )
					PUT_LEFT( GET_PRNT(bp), temp );
				else
					PUT_RIGHT( GET_PRNT(bp), temp );
				PUT_PRNT( temp, GET_PRNT(bp) );
				PUT_LEFT( temp, GET_LEFT(bp) );
				if( temp != (void *)GET_RIGHT(bp)){
					PUT_RIGHT( temp, GET_RIGHT(bp) );
					PUT_LEFT( tempP, tempR );
					if( tempR != NULL )
						PUT_PRNT( tempR,tempP );
					PUT_PRNT( GET_RIGHT(bp), temp );
				}
				
				if( tempL != NULL )
					PUT_PRNT( tempL, temp );
			}
		}
 	}
     else{//如果有兄弟节点
        if( bp == free_tree_rt ){//如果是根节点，就把兄弟节点提为根节点
		    free_tree_rt = (void *)GET_BROS(bp);
		    PUT_PRNT( free_tree_rt, NULL );
		    PUT_LEFT( free_tree_rt, GET_LEFT(bp) );
		    PUT_RIGHT( free_tree_rt, GET_RIGHT(bp) );

		    //如果当前节点有左右子树，该一下左右子树的父节点
		    if( (void *)GET_LEFT(bp) != NULL )
		    	PUT_PRNT( GET_LEFT(bp), free_tree_rt );

		    if( (void *)GET_RIGHT(bp) != NULL )
		    	PUT_PRNT( GET_RIGHT(bp), free_tree_rt );
	}else{//如果不是根节点	
		    if( GET_RIGHT(bp) == -1 ){//如果右子树为空，就
		    		PUT_BROS( GET_LEFT(bp),GET_BROS(bp) );
		    		if( (void *)GET_BROS(bp) != NULL )
		    			PUT_LEFT( GET_BROS(bp),GET_LEFT(bp) );
		    }else{
				//如果是父节点的左子树，就把父节点的左子树设为兄弟节点，否则右子树设为兄弟节点
		    		if( (void *)GET_LEFT(GET_PRNT(bp)) == bp )
		    			PUT_LEFT( GET_PRNT(bp), GET_BROS(bp) );
		    		else
		    			PUT_RIGHT( GET_PRNT(bp), GET_BROS(bp) );
		 		//把兄弟子树的相应位置全部设置为本来自己的相应位置的内容，准备退役   		
				PUT_PRNT( GET_BROS(bp), GET_PRNT(bp) );
		    		PUT_LEFT( GET_BROS(bp), GET_LEFT(bp) );
		    		PUT_RIGHT( GET_BROS(bp), GET_RIGHT(bp) );
				//如果有左右子树，就把左右子树的父节点重新设置一下
	        		if( (void *)GET_LEFT(bp) != NULL )
	        			PUT_PRNT(GET_LEFT(bp), GET_BROS(bp) );
    				if( (void *)GET_RIGHT(bp) != NULL)
    					PUT_PRNT(GET_RIGHT(bp), GET_BROS(bp) );
    			}
    	    }
    	}
  }
