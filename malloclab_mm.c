/* mm.c
 * 吴润迪 1600012806
 * segregated free list + best fit + ignore alloced block's FTRP
 * modified based on mm.textbook.c
 * nine segregated free list : <=32, <=64,..., <=4096, >4096
 * each list orgnized by block size from small to large
 * the first nine block of heap is the root pointer of each list
 * free block form: HDRP,PRED_linknode(offset),SUCC_linknode(offset)...FTRP
 * (since the heap size < 2^32, we can use offset to record the pointer)
 * alloced block do not need ftrp:
 * use the last but one bit at HDRP to record prev block alloc/free
 * when changing that HDRP, do not change that bit 
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (560)   /* Extend heap by this amount (bytes)*/ 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    
#define PUT_SAVE(p, val) (GET(p) = (GET(p) & 0x2) | (val))

/* Read the size and allocated fields from address p */
/* the last to one bit record prev block's alloc status */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)         

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

#define GET_PREV_ALLOC(bp) (GET(HDRP(bp)) & 0x2)
#define SET_NEXT_ALLOC(bp) (GET(HDRP(NEXT_BLKP(bp))) |= 0x2)
#define SET_NEXT_FREE(bp) (GET(HDRP(NEXT_BLKP(bp))) &= ~0x2)

/* Linknode offset */
#define PRED_LINKNODE(bp) ((char *)bp)
#define SUCC_LINKNODE(bp) ((char *)bp + WSIZE)

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
static char *heap_bottom = 0; /* Pointer to heap bottom */
static int listnum = 9;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static int in_heap(const void *p);
static int aligned(const void *p);

static inline char *get_ptr(unsigned int offset);
static inline unsigned int get_offset(char *bp);
static inline void insert_linknode(char *bp);
static inline void delete_linknode(char *bp);
static inline char *find_root(size_t size);
//void my_check(char *s, int lineno);

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk((listnum + 3)*WSIZE)) == (void *)-1) 
        return -1;
    heap_bottom = heap_listp;
    /* different class block pointer */
    PUT(heap_listp, 0);                          /* block size <=32 */
    PUT(heap_listp + (1*WSIZE), 0);              /* block size <=64 */
    PUT(heap_listp + (2*WSIZE), 0);              /* block size <=128 */
    PUT(heap_listp + (3*WSIZE), 0);              /* block size <=256 */
    PUT(heap_listp + (4*WSIZE), 0);              /* block size <=512 */
    PUT(heap_listp + (5*WSIZE), 0);              /* block size <=1024 */
    PUT(heap_listp + (6*WSIZE), 0);              /* block size <=2048 */
    PUT(heap_listp + (7*WSIZE), 0);              /* block size <=4096 */
    PUT(heap_listp + (8*WSIZE), 0);              /* block size > 4096 */

    PUT(heap_listp + (9*WSIZE), PACK(DSIZE, 3)); /* Prologue header */ 
    PUT(heap_listp + (10*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (11*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (10*WSIZE);                     
    SET_NEXT_ALLOC(heap_listp);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    //my_check("after init", __LINE__);
    return 0;
}

/* 
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                  
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);

    //my_check("after malloc", __LINE__);                                 
    return bp;
} 

/* 
 * free - Free a block 
 */
void free(void *bp)
{
    if (bp == 0) 
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT_SAVE(HDRP(bp), PACK(size, 0));
    PUT_SAVE(FTRP(bp), PACK(size, 0));
    SET_NEXT_FREE(bp);
    PUT(PRED_LINKNODE(bp), 0);
    PUT(SUCC_LINKNODE(bp), 0);
    coalesce(bp);

    //my_check("after free", __LINE__);
}

/*
 * realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
    size_t oldsize, asize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    oldsize = GET_SIZE(HDRP(ptr));
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);

    if (oldsize == asize)
        return ptr;
    else if (oldsize > asize)
    {
        size_t dsize = oldsize - asize;
        if (dsize >= 2*DSIZE)
        {
            PUT_SAVE(HDRP(ptr), PACK(asize, 1));
            //PUT_SAVE(FTRP(ptr), PACK(asize, 1));
            SET_NEXT_ALLOC(ptr);

            void *nbp = NEXT_BLKP(ptr);
            PUT_SAVE(HDRP(nbp), PACK(dsize, 0));
            PUT(FTRP(nbp), PACK(dsize, 0));
            SET_NEXT_FREE(nbp);

            PUT(PRED_LINKNODE(nbp), 0);
            PUT(SUCC_LINKNODE(nbp), 0);
            coalesce(nbp);
            return ptr;
        }
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }
    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    //my_check("after realloc", __LINE__);
    return newptr;
}

/* 
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_checkheap(int lineno)  
{
    if (heap_listp == 0)
    {
        //printf("heap not init, no need to check.\n");
        return;
    }
    void *bp;
    int isLastFree = 1;
    unsigned int num1_freeblock = 0;
    /* check prologue blocks*/
    if (GET(HDRP(heap_listp)) != PACK(DSIZE, 1) 
        || GET(FTRP(heap_listp)) != PACK(DSIZE, 1))
    {   
        printf("heap_listp = %p\n", heap_listp);
        printf("%x, %x\n",GET(HDRP(heap_listp)), GET(FTRP(heap_listp)));
        printf("prologue is wrong\n");
        exit(1);
    }
    /* iterately check each blocks */
    //printf("block implict list:\n");
    for (bp = NEXT_BLKP(heap_listp); bp != 0 && GET_SIZE(HDRP(bp)) > 0; 
        bp = NEXT_BLKP(bp))
    {
        
        /* does header and footer match each other? */
        if (GET(HDRP(bp)) != GET(FTRP(bp)))
        {
            printf("at line %d, header and footer of ", lineno);
            printf("block %p does not match\n", bp);
            exit(1);
        }
        /* does the block within the heap? */
        if (!in_heap(bp))
        {
            printf("at line %d, a block %p is not in heap.\n", lineno, bp);
            exit(1);
        }
        /* does the block properly aligned */
        if (!aligned(bp))
        {   
            printf("at line %d, a block %p is not aligned.\n", lineno, bp);
            exit(1);
        }
        /* check coalescing: does two free blocks adjendcy? */
        if (!GET_ALLOC(HDRP(bp)))
        {
            ++num1_freeblock;
            if (!(GET_ALLOC(HDRP(bp))) && !isLastFree)
            {
                printf("coalesing error at line %d,", lineno);
                printf(" two free blocks %p adjendcy\n", bp);
                exit(1);
            }
        }
        isLastFree = GET_ALLOC(HDRP(bp));
    }

    //printf("\nblock segregated list:\n");
    /*segregated linklist check*/
    if (heap_bottom == 0) return;
    char *root = heap_bottom;
    char *tmp = 0;
    char *succp = 0;
    unsigned int bsize = 32;
    unsigned int num2_freeblock = 0;
    for (int i = 0; i < listnum; ++i)
    {
        //printf("\nlist %d of size %d:\n", i, bsize);
        tmp = get_ptr(GET(root));
        while (tmp != NULL)
        {
            //printf("%p(size = %d)->", tmp, GET_SIZE(HDRP(tmp)));
            ++num2_freeblock;
            if (GET_ALLOC(HDRP(tmp)) != 0)
            {
                printf("at line %d, a used block %p", lineno, tmp);
                printf(" is in size %d list\n", bsize);
                exit(1);
            }
            if (!in_heap(tmp))
            {
                printf("at line %d, a free block %p in ", lineno, tmp);
                printf("size %d list is not in heap.\n", bsize);
                exit(1);
            }
            /* check whether the block is within size */
            if (bsize <= 4096 && GET_SIZE(HDRP(tmp)) > bsize)
            {
                printf("at line %d, a free block %p of ", lineno, tmp);
                printf("%d is over size %d.\n", GET_SIZE(HDRP(tmp)), bsize);
                exit(1);
            }
            /* check next/prev pointers consistent */
            succp = get_ptr(GET(SUCC_LINKNODE(tmp)));
            if (succp != NULL)
            { 
                char *pre_succp = get_ptr(GET(PRED_LINKNODE(succp)));
                if (pre_succp != tmp)
                {
                    printf("at line %d, block %p next/prev pointers ", lineno, tmp);
                    printf("are not consistent in size %d list.\n", bsize);
                    exit(1);
                }
            }
            tmp = succp;
        }
        bsize *= 2;
        root += WSIZE;
    }
    /*is freeblock num right?*/
    if (num1_freeblock != num2_freeblock)
    {
        printf("\nthe numbers of freeblock does not match:");
        printf(" %d, %d\n", num1_freeblock, num2_freeblock);
        exit(1);
    }
    //else 
    //   printf("freeblock numbers: %d\n", num1_freeblock);
    //printf("\n chcek finished.\n");
}


/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT_SAVE(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT_SAVE(FTRP(bp), PACK(size, 0));         /* Free block footer */ 
    
    /*set linknode part*/
    PUT(PRED_LINKNODE(bp), 0);
    PUT(SUCC_LINKNODE(bp), 0); 

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
    

    /* Coalesce if the previous block was free */
    bp = coalesce(bp);
    //my_check("after extend", __LINE__);
    return bp;                                          
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_PREV_ALLOC(bp);
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        //return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_linknode(NEXT_BLKP(bp));
        PUT_SAVE(HDRP(bp), PACK(size, 0));
        PUT_SAVE(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_linknode(PREV_BLKP(bp));
        PUT_SAVE(FTRP(bp), PACK(size, 0));
        PUT_SAVE(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_linknode(PREV_BLKP(bp));
        delete_linknode(NEXT_BLKP(bp));
        PUT_SAVE(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT_SAVE(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    SET_NEXT_FREE(bp);
    insert_linknode(bp);
    //my_check("after coalesce", __LINE__);
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size(4 words)
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   
    delete_linknode(bp);

    if ((csize - asize) >= (2*DSIZE)) { 
        PUT_SAVE(HDRP(bp), PACK(asize, 1));
        PUT_SAVE(FTRP(bp), PACK(asize, 1));
        SET_NEXT_ALLOC(bp);

        bp = NEXT_BLKP(bp);
        PUT_SAVE(HDRP(bp), PACK(csize-asize, 0));
        PUT_SAVE(FTRP(bp), PACK(csize-asize, 0));
        SET_NEXT_FREE(bp);
        PUT(PRED_LINKNODE(bp), 0);
        PUT(SUCC_LINKNODE(bp), 0);
        coalesce(bp);
    }
    else { 
        PUT_SAVE(HDRP(bp), PACK(csize, 1));
        PUT_SAVE(FTRP(bp), PACK(csize, 1));
        SET_NEXT_ALLOC(bp);
    }
    //my_check("after place", __LINE__);
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    char *root = find_root(asize);
    char *tmp = 0;
    while (root != heap_listp - WSIZE)
    {
        //printf("root = %p\n", root);
        tmp = get_ptr(GET(root));
        //printf("tmp = %p\n", tmp);
        while (tmp != NULL)
        {
            if (GET_SIZE(HDRP(tmp)) >= asize)
                return tmp;
            tmp = get_ptr(GET(SUCC_LINKNODE(tmp)));
        }
        root += WSIZE;
    }

    //my_check("after find_fit", __LINE__);
    return NULL;
}

/* find the root of corrspinding size */
static inline char *find_root(size_t size)
{   
    int offset = 0;
    if (size <= 32)
        offset = 0;
    else if (size <= 64)
        offset = 1;
    else if (size <= 128)
        offset = 2;
    else if (size <= 256)
        offset = 3;
    else if (size <= 512)
        offset = 4;
    else if (size <= 1024)
        offset = 5;
    else if (size <= 2048)
        offset = 6;
    else if (size <= 4096)
        offset = 7;
    else 
        offset = 8;
    //printf("end find_root offset = %d\n", offset);
    return (char *)(heap_bottom + offset * WSIZE);
}

/* insert bp to the corrsponding linklist with size-increasing */
static inline void insert_linknode(char *bp)
{
    unsigned int bpsize = GET_SIZE(HDRP(bp));
    char *root = find_root(bpsize);
    char *tmp = get_ptr(GET(root));
    char *pred = root;
    while (tmp != NULL && (GET_SIZE(HDRP(tmp)) < bpsize))
    {
        pred = tmp;
        tmp = get_ptr(GET(SUCC_LINKNODE(tmp)));
    }
    //printf("pred = %p, bp = %p, tmp = %p\n", pred, bp, tmp);
    if (pred == root)
    {
        PUT(root, get_offset(bp));
        PUT(PRED_LINKNODE(bp), 0);
        PUT(SUCC_LINKNODE(bp), get_offset(tmp));
        if (tmp != NULL)
            PUT(PRED_LINKNODE(tmp), get_offset(bp));
    }
    else
    {
        PUT(SUCC_LINKNODE(pred), get_offset(bp));
        PUT(PRED_LINKNODE(bp), get_offset(pred));
        PUT(SUCC_LINKNODE(bp), get_offset(tmp));
        if (tmp != NULL)
            PUT(PRED_LINKNODE(tmp), get_offset(bp));
    }
    //my_check("after insert", __LINE__);
}

/* delete bp */
static inline void delete_linknode(char *bp)
{
    char *root = find_root(GET_SIZE(HDRP(bp)));
    char *pred = get_ptr(GET(PRED_LINKNODE(bp)));
    char *succ = get_ptr(GET(SUCC_LINKNODE(bp)));
    if (pred == NULL)
    {
        PUT(root, get_offset(succ));
        if (succ != NULL)
            PUT(PRED_LINKNODE(succ), 0);
    }
    else
    {
        PUT(SUCC_LINKNODE(pred), get_offset(succ));
        if (succ != NULL)
            PUT(PRED_LINKNODE(succ), get_offset(pred));
    }
    PUT(PRED_LINKNODE(bp), 0);
    PUT(SUCC_LINKNODE(bp), 0);

    //my_check("after delete_linknode", __LINE__);
}

/* use 4-bytes offset to get 8-bytes pointer*/
static inline char * get_ptr(unsigned int offset)
{
    return offset == 0? NULL: (char *)(heap_bottom + offset);
}

/* use 8-bytes pointer to get 4-bytes offset */
static inline unsigned int get_offset(char *bp)
{
    return bp == NULL?0: (unsigned int)(bp - heap_bottom);
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

