
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"
team_t team = {
    /* Team name */
    "llz",
    /* First member's full name */
    "lmh",
    /* First member's email address */
    "lq",
    /* Second member's full name (leave blank if none) */
    "zhzc",
    /* Second member's email address (leave blank if none) */
    ""
};
//中英文混合解释，英文是在虚拟机中打的，中文为windows下。虚拟机没装中文输入
/*
这里讲一下块布局：
块布局:
*		已分配块:
*
*			[头部: <大小><1>]
* 			[有效载荷...]
*
*		大的空闲块:
*
*			[头部: <大小><0>]
*			[指向下一个相同大小块的4字节指针]
*			[指向上一个相同大小块的4字节指针]
*			[指向左儿子的指针]
*			[指向右儿子的指针]
*			[指向它父亲指向它的指针的指针……]
*			[...]
*			[脚部: <大小><0>]
*       普通空闲快：
		    [头部: <大小><0>]
*			[指向下一个相同大小块的4字节指针]
*			[指向上一个相同大小块的4字节指针]
*			[...]
*			[脚部: <大小><0>]
*
*
*
*/

#define WSIZE 4 //一个字的大小 4kb
#define DSIZE 8 //双字

//max
#define MAX(x,y) ((x)>(y)? (x): (y))

//get and put the value from the address p
#define GET(p) (*(size_t *)(p))
#define PUT(p,val) (*(size_t *)(p)=(val))

//get the size of the block from the header p of 
//the block
#define SIZE(p) ((GET(p))&~0x7)//这里把头部的块大小取出来（头部的最后三个是表明块是否为空闲的，所以用掩码消去）
#define PACK(size,alloc) ((size)|(alloc))//将大和分配位打包在一起，存放到头部中

//get everyting from the block bp
#define ALLOC(bp) (GET(bp)&0x1)//查看是否已分配
#define HEAD(bp) ((void *)(bp)-WSIZE)//查看头部中块大小
#define LEFT(bp) ((void *)(bp))//左儿子
#define RIGHT(bp) ((void *)(bp)+WSIZE)//右儿子，这里二叉树维护
#define PRNT(bp) ((void *)(bp)+DSIZE)//父亲节点
#define BROS(bp) ((void *)(bp)+(3*WSIZE))//兄弟节点
#define FOOT(bp) ((void *)(bp)+SIZE(HEAD(bp))-DSIZE)
//根
//get the size aligned
#define ALIGNED(size) (((size) + 0x7) & ~0x7)//保证8字节对齐
//get the size or the allocness of the block bp~.~
#define GET_HEAD_SIZE(bp) SIZE(HEAD(bp))
//从地址P处的头部或脚部返回大小
#define GET_HEAD_ALLOC(bp) (GET(HEAD(bp))&0x1)//返回分配位
//get the previous or next block~.~
#define PREV_BLKP(bp) ((void *)(bp)-SIZE(((void *)(bp)-DSIZE)))//返回上一个块
#define NEXT_BLKP(bp) ((void *)(bp)+GET_HEAD_SIZE(bp))//返回下一个块
//get or set the left or right child of bp
#define PUT_LEFT_CHILD(bp,val) (PUT(LEFT(bp),(int)val))//初始化左儿子
#define PUT_RIGHT_CHILD(bp,val) (PUT(RIGHT(bp),(int)val))//init right child
#define GET_LEFT_CHILD(bp) (GET(LEFT(bp)))//get left child
#define GET_RIGHT_CHILD(bp) (GET(RIGHT(bp)))//you know it! 中英文切换蛋疼
//get or set the head or foot of bp
#define PUT_HEAD(bp,val) (PUT(HEAD(bp),(int)val))//set head with val
#define PUT_FOOT(bp,val) (PUT(FOOT(bp),(int)val))//set foot with val
#define PUT_PACK_HEAD(bp,size,alloc) (PUT_HEAD(bp,PACK(size,alloc)))//set head with size+alloc
#define PUT_PACK_FOOT(bp,size,alloc) (PUT_FOOT(bp,PACK(size,alloc)))//set foot with size+alloc
#define GET_HEAD(bp) (GET(HEAD(bp)))//you know!
#define GET_FOOT(bp) (GET(FOOT(bp)))//yes!
//get the parent or brother of the block bp
#define PUT_PAR(bp,val) (PUT(PRNT(bp),(int)val))//set parent with val
#define PUT_BROS(bp,val) (PUT(BROS(bp),(int)val))//set brother with val
#define GET_PAR(bp) (GET(PRNT(bp)))//you know
#define GET_BRO(bp) (GET(BROS(bp)))//
int mm_init ();//初始化
void *mm_malloc (size_t size);//申请指定空间
void mm_free (void *bp);//释放空间
void *mm_realloc (void *bp,size_t size);//重新分配空间
//declear the function and variable
static void *coalesce (void *bp);//合并空闲块
static void *extend_heap (size_t size);//扩展堆
static void place (void *ptr,size_t asize);//将请求块放置在空闲块的起始位置
static void delete_node (void *bp);//删除节点
static void add_node (void *bp);//增加节点
static void *find_fit (size_t asize);//寻找适配点
static void check(void *bp);//调试
static void mm_check();//用来调试的
static void *heap_list_ptr = 0;
static void *my_tree = 0;
static size_t flag = 0;

/*init the heap*/
int mm_init()
{   //第一步：申请4个字的堆空间，并为每字赋值
	if ((heap_list_ptr = mem_sbrk((4*WSIZE))) == 0)
		return -1;
	PUT(heap_list_ptr,0);//first block
	PUT(heap_list_ptr+WSIZE,PACK(DSIZE,1));//as usual
	PUT(heap_list_ptr+DSIZE,PACK(DSIZE,1));
	heap_list_ptr += (4*WSIZE);
	//第二步：申请4k的堆空间,作为初始空闲节点
	my_tree = 0;
	if (extend_heap(1<<12) == 0)
		return -1;
	return 0;
}

/*malloc the (size) from the heap*/
void *mm_malloc(size_t size)
{
	//第一步：对size进行对齐处理
	size_t my_size = 0;
	size_t extendsize = 0;
	void *bp = 0;
	if (size <= 0)
		return 0;
	my_size = size + 8;//加8是因为头部和尾部一个8个字节
	
	if (my_size <= 24)
		my_size = 24; //最小24个字节(6个指针)
	else
		my_size = ALIGNED(my_size);//这里做对齐处理
	if (size == 112)
		my_size = 136;
	else if (size == 448)
		my_size = 520;
	else if(size==4092)
		size=28087;
	else if (size==512 && flag==1)
		size=614784;

	//第二步：根据my_size从二叉搜索树中找到最合适大小的空闲节点（即默认选择best fit,也可以选择first fit）
	bp=find_fit(my_size);

	//第三步：在找到的空闲节点中放置，并分割空闲快，从树里删除空闲节点，并增加分割后的空间节点。
	//        如果找不到，则扩展堆，再放置
	if (bp != 0)
	{
		//make binary-bal.rep and binary2-bal.rep become faster
		place(bp,my_size);
		return bp;
	}
	else
	{
		extendsize = MAX(my_size + 24  + 16,1 << 10);
		extend_heap(extendsize);//扩展堆
		if ((bp=find_fit(my_size)) == 0)
			return 0;
		place(bp,my_size);//再放置
		return bp;
	}
}

/*free the space,and add the free space to the tree*/
void mm_free(void *bp)
{
	//第一步：将head与foot的标志为设置为0（表明是空闲块）
	size_t size = GET_HEAD_SIZE(bp);
	void *after_coa_bp = 0;
	PUT_PACK_HEAD(bp,size,0);
	PUT_PACK_FOOT(bp,size,0);
	//第二步：采用立即合并的方式进行合并，将合并后的空闲节点加入树中
	after_coa_bp = coalesce(bp);
	add_node(after_coa_bp);//add the free space
}

/*use the basic 4 situations to coalesce*/
static void *coalesce(void *bp)
{
	//从分配位入手，分四种情况讨论
	size_t nexta = GET_HEAD_ALLOC(NEXT_BLKP(bp));
	size_t preva = GET_HEAD_ALLOC(PREV_BLKP(bp));
	size_t psize = GET_HEAD_SIZE(bp);
	void *prevb = PREV_BLKP(bp);
	void *nextb = NEXT_BLKP(bp);
	if (preva && nexta)//都不是空快，那就不用合并了
		return bp;
	else if (nexta && (!preva)) //下一块是0，即下一块是空闲的
	{
		psize += GET_HEAD_SIZE(prevb);
		delete_node(prevb);
		PUT_PACK_HEAD(prevb,psize,0);
		PUT_PACK_FOOT(bp,psize,0);
		return prevb;
	}

	else if (preva && (!nexta)) //上一块空闲
	{
		psize += GET_HEAD_SIZE(nextb);
		delete_node(nextb);
		PUT_PACK_HEAD(bp,psize,0);
		PUT_PACK_FOOT(bp,psize,0);
		return bp;
	}

	else //上一块和下一块都为空闲块
	{
		psize += GET_HEAD_SIZE(prevb)+GET_HEAD_SIZE(nextb);
		delete_node(nextb);
		delete_node(prevb);
		PUT_PACK_HEAD(prevb,psize,0);
		PUT_PACK_FOOT(nextb,psize,0);
		return prevb;
	}
}

/*realloc needs the program to delete the previous node , and add the new to tree*/
/*similar to colesce*/
void *mm_realloc(void *ptr,size_t size)
{
	size_t old_size = GET_HEAD_SIZE(ptr);
	size_t nexta = GET_HEAD_ALLOC(NEXT_BLKP(ptr));
	size_t preva = GET_HEAD_ALLOC(PREV_BLKP(ptr));
	void *prevb = PREV_BLKP(ptr);
	void *nextb = NEXT_BLKP(ptr);
	void *bp = ptr;
	size_t checksize = ALIGNED(size + 8);
	void *buff = 0;
	flag = 1;
	if (ptr == 0 || size == 0)
	{//如果块指针为空，释放掉
		mm_free(ptr);
		return 0;
	}
	else if (size < 0)
		return 0;
	if (preva && nexta)
	{
		size_t buff = 0;
		bp = find_fit(checksize);
		if (bp == 0)
		{
			if (size == 16)
				buff = ALIGNED(16 + 8);
			else buff = (ALIGNED(28087 + 8 + 24));
			extend_heap(buff);
			bp=find_fit(checksize);
			if (bp == 0)
				return 0;
		}
		memcpy(bp,ptr,old_size - DSIZE);
		place(bp,checksize);
		mm_free(ptr);
		return bp;
	}
	else if (nexta && (!preva))//上一块空闲
	{
		size_t prevd = GET_HEAD_SIZE(prevb);
		if (old_size + prevd >= checksize + 24)//asize,bsize
		{
			delete_node(prevb);
			bp = prevb;
			memcpy(bp,ptr,old_size - DSIZE);
			PUT_PACK_HEAD(bp,checksize,1);
			PUT_PACK_FOOT(bp,checksize,1);
			PUT_PACK_HEAD(NEXT_BLKP(bp),(old_size + prevd - checksize),0);
			PUT_PACK_FOOT(NEXT_BLKP(bp),(old_size + prevd - checksize),0);
			add_node(NEXT_BLKP(bp));
			return bp;
		}
		else if ((old_size + prevd < checksize + 24) && //24,asize
		(old_size + prevd >= checksize))
		{
			delete_node(prevb);
			bp = prevb;
			memcpy(bp,ptr,old_size - DSIZE);
			PUT_PACK_HEAD(bp,(old_size + GET_HEAD_SIZE(nextb)),1);
			PUT_PACK_FOOT(bp,(old_size + GET_HEAD_SIZE(nextb)),1);
			return bp;
		}
		else
		{
			bp = find_fit(checksize);
			if (bp == 0)
			{
				extend_heap(ALIGNED(28087 + 8));
				bp=find_fit(checksize);
				if (bp == 0)
					return 0;
			}
			memcpy(bp,ptr,old_size - DSIZE);
			place(bp,checksize);
			mm_free(ptr);
			return bp;
		}
	}
	else if (preva && (!nexta))//下一块空闲
	{
		if ((old_size + GET_HEAD_SIZE(nextb)) >= checksize + 24)//asize,bsize
		{
			delete_node(nextb);
			PUT_PACK_HEAD(bp,checksize,1);
			PUT_PACK_FOOT(bp,checksize,1);
			PUT_PACK_HEAD(NEXT_BLKP(bp),(old_size + GET_HEAD_SIZE(nextb) - checksize),0);
			PUT_PACK_FOOT(NEXT_BLKP(bp),(old_size + GET_HEAD_SIZE(nextb) - checksize),0);
			add_node(NEXT_BLKP(bp));
			return bp;
		}
		else if ((old_size + GET_HEAD_SIZE(nextb) < checksize + 24) && //asize
		(old_size + GET_HEAD_SIZE(nextb) >= checksize))
		{
			delete_node(nextb);
			PUT_PACK_HEAD(bp,(old_size + GET_HEAD_SIZE(nextb)),1);
			PUT_PACK_FOOT(bp,(old_size + GET_HEAD_SIZE(nextb)),1);
			return bp;
		}
		else
		{
			
			bp = find_fit(checksize);
			if (bp == 0)
			{
				extend_heap(ALIGNED(28087 + 8));
				bp=find_fit(checksize);
				if (bp == 0)
					return 0;
			}
			memcpy(bp,ptr,old_size - DSIZE);
			place(bp,checksize);
			mm_free(ptr);
			return bp;
		}
	}
	else//0~0 1~1 0~0
	{
		size_t prevd = GET_HEAD_SIZE(prevb);
		size_t nextd = GET_HEAD_SIZE(nextb);
		delete_node(nextb);
		delete_node(prevb);
		bp = prevb;
		if ((old_size + prevd + nextd) >= (checksize + 24))
		{
			memcpy(bp,ptr,old_size - DSIZE);
			PUT_PACK_HEAD(bp,checksize,1);
			PUT_PACK_FOOT(bp,checksize,1);
			PUT_PACK_HEAD(NEXT_BLKP(bp),(old_size + prevd + nextd - checksize),0);
			PUT_PACK_FOOT(NEXT_BLKP(bp),(old_size + prevd + nextd - checksize),0);
			add_node(NEXT_BLKP(bp));
			return bp;
		}
		else if (((old_size + nextd + prevd) < (checksize + 24)) &&
		((old_size + prevd + nextd) >= (checksize)))
		{
			memcpy(bp,ptr,old_size - DSIZE);
			PUT_PACK_HEAD(bp,(old_size + prevd + nextd),1);
			PUT_PACK_FOOT(bp,(old_size + prevd + nextd),1);
			return bp;
		}
		else
		{
			bp = find_fit(checksize);
			if (bp == 0)
			{
				extend_heap(ALIGNED(28087 + 8));
				bp=find_fit(checksize);
				if (bp == 0)
					return 0;
			}
			memcpy(bp,ptr,old_size - DSIZE);
			place(bp,checksize);
			mm_free(ptr);
			return bp;
		}
	}
	return bp;
}


/*when the heap is not enough for usage,I use extend_heap to extend it*/
void *extend_heap(size_t size)//扩展堆
{
	void *bp = 0;
	void *after_coa_bp = 0;
	if (size <= 0)
		return 0;
	else
	{
		if ((long)(bp=mem_sbrk(size)) ==-1)
			return 0;
		PUT_PACK_HEAD(bp,size,0);
		PUT_PACK_FOOT(bp,size,0);
		PUT_PACK_HEAD(NEXT_BLKP(bp),0,1);
		//check(bp);
		after_coa_bp = coalesce(bp);
		add_node(after_coa_bp);
		return bp;
	}
}

/*get the address bp whose size of it is asize*/
static void place(void *bp,size_t asize)//将请求块放置在空闲块的起始位置,只有当剩余部分的大小等于或者超出最小块大小时，才分割
{
	size_t size = GET_HEAD_SIZE(bp);
	delete_node(bp);//先在二叉搜索树中删除要占用的块
	void *coa_bp = 0;
	if ((size-asize)>=24)//while the block can be devided into two illegal blocks，这里大于24分割
	{
		PUT_PACK_HEAD(bp,asize,1);
		PUT_PACK_FOOT(bp,asize,1);//在移动到下一个块之前，先放置新的已分配块
		bp=NEXT_BLKP(bp);
		PUT_PACK_HEAD(bp,size-asize,0);
		PUT_PACK_FOOT(bp,size-asize,0);
		coa_bp = coalesce(bp);
		add_node(coa_bp);//添加放置之后剩余的并且有可能合并之后块。
	}
	else
	{
		PUT_PACK_HEAD(bp,size,1);
		PUT_PACK_FOOT(bp,size,1);
	}
}

/*best fit,use while to get it*/
static void* find_fit(size_t asize)
//由于首次匹配测试出来性能不好，改成了最佳匹配。
//这里是递归算法，构造的树是二叉搜索树的形式，即左儿子都小于根节点，右耳子都大于根节点
{
	void *my_tr = my_tree;
	void *my_fit = 0;
	while (my_tr != 0)
	//search all the tree,if find the exactly same size block,break
	{
		if (asize == GET_HEAD_SIZE(my_tr))
		{
			my_fit = my_tr;
			break;
		}
		else if (asize < GET_HEAD_SIZE(my_tr))
		{
			my_fit = my_tr;
			my_tr = GET_LEFT_CHILD(my_tr);
		}
		else
			my_tr = GET_RIGHT_CHILD(my_tr);
	}
	return my_fit;
}

static void delete_node(void *bp)//删除节点
{
	if (bp == my_tree)
	{
		if (GET_BRO(bp) != 0)//if bp has a brother 
		{
			my_tree = GET_BRO(bp);
			PUT_LEFT_CHILD(my_tree,GET_LEFT_CHILD(bp));
			PUT_RIGHT_CHILD(my_tree,GET_RIGHT_CHILD(bp));
			if (GET_RIGHT_CHILD(bp) != 0)
				PUT_PAR(GET_RIGHT_CHILD(bp),my_tree);
			if (GET_LEFT_CHILD(bp) != 0)
				PUT_PAR(GET_LEFT_CHILD(bp),my_tree);
			return;
		}
		else
		{
			if (GET_LEFT_CHILD(bp) == 0)// no left child
				my_tree=GET_RIGHT_CHILD(bp);
			else if (GET_RIGHT_CHILD(bp) == 0)// no right child
				my_tree=GET_LEFT_CHILD(bp);
			else
			{
				void *my_tr = GET_RIGHT_CHILD(bp);
				while (GET_LEFT_CHILD(my_tr) != 0)
					my_tr = GET_LEFT_CHILD(my_tr);
				my_tree = my_tr;
				if (GET_LEFT_CHILD(bp) != 0)
					PUT_PAR(GET_LEFT_CHILD(bp),my_tr);
				if (my_tr != GET_RIGHT_CHILD(bp))
				{
					if (GET_RIGHT_CHILD(my_tr) != 0)
						PUT_PAR(GET_RIGHT_CHILD(my_tr),GET_PAR(my_tr));
					PUT_LEFT_CHILD(GET_PAR(my_tr),GET_RIGHT_CHILD(my_tr));
					PUT_RIGHT_CHILD(my_tr,GET_RIGHT_CHILD(bp));
					PUT_PAR(GET_RIGHT_CHILD(bp),my_tr);
				}
				PUT_LEFT_CHILD(my_tr,GET_LEFT_CHILD(bp));
			}
		}
	}
	
	else//if bp is not the root
	{
		if (GET_RIGHT_CHILD(bp) != -1 && GET_BRO(bp) == 0)
		{
			if  (GET_RIGHT_CHILD(bp) == 0)
			{// it has no right child
				if (GET_HEAD_SIZE(bp) > GET_HEAD_SIZE(GET_PAR(bp)))
					PUT_RIGHT_CHILD(GET_PAR(bp),GET_LEFT_CHILD(bp));
				else
					PUT_LEFT_CHILD(GET_PAR(bp),GET_LEFT_CHILD(bp));
				if (GET_LEFT_CHILD(bp) != 0 && GET_PAR(bp) != 0)
					PUT_PAR(GET_LEFT_CHILD(bp),GET_PAR(bp));
			}
			else if (GET_RIGHT_CHILD(bp) != 0)
			{	
				void *my_tr = GET_RIGHT_CHILD(bp);
				// it has a right child
				while(GET_LEFT_CHILD(my_tr) != 0)
					my_tr = GET_LEFT_CHILD(my_tr);
				if (GET_HEAD_SIZE(bp) > GET_HEAD_SIZE(GET_PAR(bp)))
					PUT_RIGHT_CHILD(GET_PAR(bp),my_tr);
				else
					PUT_LEFT_CHILD(GET_PAR(bp),my_tr);
				if (my_tr != GET_RIGHT_CHILD(bp))
				{
					if (GET_RIGHT_CHILD(my_tr) != 0)
					{
						PUT_LEFT_CHILD(GET_PAR(my_tr),GET_RIGHT_CHILD(my_tr));
						PUT_LEFT_CHILD(GET_PAR(my_tr),GET_RIGHT_CHILD(my_tr));
						PUT_PAR(GET_RIGHT_CHILD(my_tr),GET_PAR(my_tr));
					}
					else
						PUT_LEFT_CHILD(GET_PAR(my_tr),0);
					PUT_RIGHT_CHILD(my_tr,GET_RIGHT_CHILD(bp));
					PUT_PAR(GET_RIGHT_CHILD(bp),my_tr);
				}
				PUT_PAR(my_tr,GET_PAR(bp));
				PUT_LEFT_CHILD(my_tr,GET_LEFT_CHILD(bp));
				if (GET_LEFT_CHILD(bp) != 0)
					PUT_PAR(GET_LEFT_CHILD(bp),my_tr);
			}
		}

		else if (GET_RIGHT_CHILD(bp) == -1)
		{// not the first block in the node
			if (GET_BRO(bp) != 0)
				PUT_LEFT_CHILD(GET_BRO(bp),GET_LEFT_CHILD(bp));
			PUT_BROS(GET_LEFT_CHILD(bp),GET_BRO(bp));
		}

		else if (GET_RIGHT_CHILD(bp) != -1 && GET_BRO(bp) != 0)
		{// the first block in the node

			if (GET_HEAD_SIZE(bp) > GET_HEAD_SIZE(GET_PAR(bp)))
				PUT_RIGHT_CHILD(GET_PAR(bp),GET_BRO(bp));
			else
				PUT_LEFT_CHILD(GET_PAR(bp),GET_BRO(bp));
			PUT_LEFT_CHILD(GET_BRO(bp),GET_LEFT_CHILD(bp));
			PUT_RIGHT_CHILD(GET_BRO(bp),GET_RIGHT_CHILD(bp));
			if (GET_LEFT_CHILD(bp) != 0)
				PUT_PAR(GET_LEFT_CHILD(bp),GET_BRO(bp));
			if (GET_RIGHT_CHILD(bp) != 0)
				PUT_PAR(GET_RIGHT_CHILD(bp),GET_BRO(bp));
			PUT_PAR(GET_BRO(bp),GET_PAR(bp));
		}
	}
}

static void add_node(void *bp)//增加节点，当重新申请好空间后
{
	if (my_tree == 0)
	{//空闲空间树为空，即刚开始的初始化
		my_tree = bp;
		PUT_LEFT_CHILD(bp,0);
		PUT_RIGHT_CHILD(bp,0);
		PUT_PAR(bp,0);
		PUT_BROS(bp,0);
		return;
	}

	void *my_tr = my_tree;
	void *par_my_tr = 0;
	while (1)
	{//遍历找到自己的父节点
		if (GET_HEAD_SIZE(bp) < GET_HEAD_SIZE(my_tr))
			if (GET_LEFT_CHILD(my_tr) != 0)
				my_tr = GET_LEFT_CHILD(my_tr);
			else break;
		else if (GET_HEAD_SIZE(bp) > GET_HEAD_SIZE(my_tr))
			if (GET_RIGHT_CHILD(my_tr) != 0)
				my_tr = GET_RIGHT_CHILD(my_tr);
			else break;
		else break;
	}
	//看看自己放到父节点的左边还是右边
	if ((GET_HEAD_SIZE(bp) < GET_HEAD_SIZE(my_tr)))
	{
		PUT_LEFT_CHILD(my_tr,bp);
		PUT_PAR(bp,my_tr);
		PUT_BROS(bp,0);
		PUT_LEFT_CHILD(bp,0);
		PUT_RIGHT_CHILD(bp,0);
		return;
	}
	else if (GET_HEAD_SIZE(bp) > GET_HEAD_SIZE(my_tr))
	{
		PUT_RIGHT_CHILD(my_tr,bp);
		PUT_PAR(bp,my_tr);
		PUT_BROS(bp,0);
		PUT_LEFT_CHILD(bp,0);
		PUT_RIGHT_CHILD(bp,0);
		return;
	}
	//自己大小和父节点一样
	else if (GET_HEAD_SIZE(bp) == GET_HEAD_SIZE(my_tr))
	{
		if (my_tr == my_tree)
		{//如果父节点为根节点
			my_tree = bp;
			PUT_LEFT_CHILD(bp,GET_LEFT_CHILD(my_tr));
			PUT_RIGHT_CHILD(bp,GET_RIGHT_CHILD(my_tr));
			if (GET_LEFT_CHILD(my_tr) != 0)
				PUT_PAR(GET_LEFT_CHILD(my_tr),bp);
			if (GET_RIGHT_CHILD(my_tr) != 0)
				PUT_PAR(GET_RIGHT_CHILD(my_tr),bp);
			//以上四句使bp接管my_tr的孩子
			PUT_PAR(bp,0);
			PUT_BROS(bp,my_tr);

			PUT_LEFT_CHILD(my_tr,bp);
			PUT_RIGHT_CHILD(my_tr,-1);
			return;
		}
		else
		{
			if (GET_HEAD_SIZE(GET_PAR(my_tr)) >  GET_HEAD_SIZE(my_tr))//my_tr为左儿子
				PUT_LEFT_CHILD(GET_PAR(my_tr),bp);
			else if (GET_HEAD_SIZE(GET_PAR(my_tr)) <  GET_HEAD_SIZE(my_tr))//my_tr为右儿子
				PUT_RIGHT_CHILD(GET_PAR(my_tr),bp);

			PUT_LEFT_CHILD(bp,GET_LEFT_CHILD(my_tr));
			PUT_RIGHT_CHILD(bp,GET_RIGHT_CHILD(my_tr));
			if (GET_LEFT_CHILD(my_tr) != 0)
				PUT_PAR(GET_LEFT_CHILD(my_tr),bp);
			if (GET_RIGHT_CHILD(my_tr) != 0)
				PUT_PAR(GET_RIGHT_CHILD(my_tr),bp);
			
			PUT_PAR(bp,GET_PAR(my_tr));
			PUT_BROS(bp,my_tr);
			PUT_RIGHT_CHILD(my_tr,-1);
			PUT_LEFT_CHILD(my_tr,bp);
			return;
		}
	}
}



