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
	"team2",
	/* First member's full name */
	"Byeonghyeon Kim",
	/* First member's email address */
	"kimbh7391@gmail.com",
	/* Second member's full name (leave blank if none) */
	"Euihoon Kim",
	/* Third member's full name (leave blank if none) */
	"Seojin Lee"
};

/*------------------------------------------------------------------------------------------------------------------------------------------------------*/

#define WSIZE 4															 // [bytes] word, header, footer size
#define DSIZE 8															 // [bytes] double word size
#define CHUNKSIZE (1<<12)												 // [bytes] extend heap by this amount 하나의 페이지는 4[kb]

#define MAX(x,y)		 ((x)>(y) ? (x):(y))							 // max 값 반환

#define PACK(size,alloc) ((size) | (alloc))								 // size 뒤의 000 공간에 allocation 여부를 저장한 비트를 반환

#define GET(p)			 (*(unsigned int *)(p))							 // 주소값에서 값 읽어옴
#define PUT(p,val)		 (*(unsigned int *)(p) = (val))					 // 주소값에다 값 씀

#define GET_SIZE(p)		 (GET(p) & ~0x7)							     // 블록 사이즈 읽어옴
#define GET_ALLOC(p)	 (GET(p) & 0x1)								     // 할당 여부를 읽어옴
																		 // bp = block pointer
#define HDRP(bp)		 ((char*)(bp) - WSIZE)							 // 헤더의 주소값을 반환
#define FTRP(bp)		 ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)		 // 푸터의 주소값을 반환, 헤더에서 사이즈를 안 다음 double word를 빼줌.

																		 // blkp = block pointer
#define NEXT_BLKP(bp) 	 ((char*)(bp) + GET_SIZE(((char *)(bp) -WSIZE))) // 다음 블록의 주소값을 반환, 헤더에서 내 사이즈 더해주고 word를 빼줌.
#define PREV_BLKP(bp) 	 ((char*)(bp) - GET_SIZE(((char *)(bp) -DSIZE))) // 전 블록의 주소값을 반환, 헤더에서 double word를 빼고 전 블록의 사이즈를 알아낸다.                                                   

#define GET_P(p)		 ((char*)*(unsigned int *)(p))					 // 주소값에서 주소값을 읽어옴 ( GET 을 써도 되지만 직관적이기 위해)
#define PUT_P(p,val)	 (*(unsigned int *)(p) = (int)(val))			 // 주소값에 주소값을 넣음 ( PUT을 써도 되지만 직관적이기 위해)

#define NEXTRP(bp)		 ((char*)(bp) + WSIZE)							 // 다음 free를 담는 word 주소
#define PREVRP(bp)		 ((char*)(bp))									 // 이전 free를 담는 word 주소

#define NEXT_FREE_BLKP(bp)  (GET_P((char *)(bp) + WSIZE))				 // 다음 FREE BLOCK POINTER
#define PREV_FREE_BLKP(bp)  (GET_P((char *)(bp)))						 // 이전 FREE BLOCK POINTER

#define CHANGE_PREV(bp,val) (PUT_P(PREVRP(bp), val));                    // 블록의 PREV word에 주소값 val을 넣어줌
#define CHANGE_NEXT(bp,val) (PUT_P(NEXTRP(bp), val));                    // 블록의 NEXT word에 주소값 val을 넣어줌

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);

// explit에 추가된 함수
static void cut_link(void* bp);
static void push_first(void* bp);

// segregated에 추가된 함수
static void seg_init(void);
static void* seg_find(int size);

static char* heap_listp;												 // heap의 첫 번째 pointer-------------------------------------------------------
static char* seg_listp;										    		 // segrated의 주소들을 담는 곳의 첫번째를 가리키는 pointer----------------------


void seg_init(void) {													 // segregated list를 만드는 함수 -----------------------------------------------

	if ((seg_listp = mem_sbrk(32 * WSIZE)) == (void*)-1) return;		 // segregated list 만들 공간 할당

	for (int i = 0; i < 32; i++) {										 // 2^0 부터 2^32 까지 NULL값으로 초기화
		PUT_P(seg_listp + (i * WSIZE), NULL);
	}
}

static void* seg_find(int size) {										 // size에 맞는 segregated point 찾는 함수---------------------------------------
	static char* seg;

	int i = 0;
	for (i = 32; i > 0; i--) {				 							 // 2^32 부터 비트연산으로 적당한 값을 찾음   
		if ((size & (1 << (i))) > 0) {
			break;
		}
	}
	seg = seg_listp + (i * WSIZE);										 // 2^n 에 맞는 n 번째 segretated 주소 반환

	return seg;
}

int mm_init(void)														 // 메모리 처음 만들기
{
	seg_init();															 // segregated list 만들기

	if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void*)-1) return -1;	   	 // mem_sbrk 호출해서 4W 메모리 request하는 데, 실패 하면 -1 리턴
	PUT(heap_listp, 0);													 // heap:0에  free 넣음 (Alignment padding)
	PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1));					 // heap:1에  DSIZE와 allocated 넣음 (PROLOGUE HEADER)
	PUT_P(heap_listp + (2 * WSIZE), NULL);								 // heap:2 previous free block pointer 는 null
	PUT_P(heap_listp + (3 * WSIZE), NULL);								 // heap:3 next free block pointer 는 null
	PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1));					 // heap:4에  DSIZE와 allocated 넣음 (PROLOGUE PUTTER)
	PUT(heap_listp + (5 * WSIZE), PACK(0, 1));							 // heap:5에  allocated 넣음 (EPILOGUE HEADER)
	heap_listp += (2 * WSIZE);											 // heap_lisp 포인터를 옮겨줌

	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)                          // chunk size 확인(받을수 있는 사이즈인지)
		return -1;

	return 0;
}

static void* extend_heap(size_t words) {								 // 힙을 넘어간다면 힙을 추가로 받아옴---------------------------------------------
	char* bp;
	size_t size;

	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;			 // 짝수로 만듬
	if ((long)(bp = mem_sbrk(size)) == -1)								 // 너무 커서 할당 못받으면 return -1
		return NULL;

	PUT(HDRP(bp), PACK(size, 0));										 // block header free
	PUT(FTRP(bp), PACK(size, 0));                                        // block putter free
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));								 // 새로운 epiloge 헤더

	return coalesce(bp);												 // 만약 전 block이 프리였다면 합친다.
}

void* mm_malloc(size_t size)											 // 메모리할당-----------------------------------------------------------------------
{
	size_t asize;														 // 생성할 size
	size_t extendsize;													 // 만약 chunksize를 넘긴 사이즈
	char* bp;

	if (size == 0)														 // 만약 입력받은 사이즈가 0 이면 무시
		return NULL;

	if (size <= DSIZE)													 // 만약 입력받은 사이즈가 dsize보다 작아도 최소 size로 생성
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + (DSIZE)+(DSIZE - 1)) / DSIZE);		     // 8의 배수(Dsize)로 생성

	if ((bp = find_fit(asize)) != NULL) {								 // 들어갈 free 블록이 있다면 넣어준다.
		place(bp, asize);
		return bp;
	}

	extendsize = MAX(asize, CHUNKSIZE);								     // 만약 chunksize를 넘긴 사이즈라면
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)					 // 넘긴 사이즈만큼의 힙을 할당받음
		return NULL;

	place(bp, asize);

	return bp;
}


static void* find_fit(size_t asize) {									 // 들어갈 자리를 찾는 함수  best fit -------------------------------------------------------
	void* bp;
	void* best_bp = (char*)NULL;

	size_t best;

	static char* seg;

	int i = 0;
	for (i = 32; i > 0; i--) { 		 									 // 2^32 부터 비트연산으로 적당한 값을 찾음 (작은값은 필요없다.) 
		if ((asize & (1 << (i))) > 0) {
			break;
		}
	}

	int j = i;
	for (j = i; j <= 32; j++) {											 // 적당한 값부터 탐색 시작
		seg = seg_listp + (j * WSIZE);
		if (GET_P(seg) != (char*)NULL) {								 // n번째 주소가 비어있지 않다면 탐색한다.
			best = (1 << (j + 1));									     // best 값을 비교하기 위한 초기값
			for (bp = PREV_FREE_BLKP(seg); bp != (char*)NULL; bp = PREV_FREE_BLKP(bp)) {	// segregated list부터 찾아서 들어감
				if (asize <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) - asize < best) {     // block이 주어진 사이즈보다 fit하고 best라면
					best_bp = bp;
					best = GET_SIZE(HDRP(bp)) - asize;										// best 블록의 주소값을 저장해둠
					//return bp;
				}
			}
			if (best_bp != (char*)NULL) {
				return best_bp;											// 찾은 best 블록이 있다면 반환
			}
		}
	}

	return NULL;														// 못 찾았다면 null 반환, extend 받게될 것
}
static void place(void* bp, size_t asize) {                               // free 블록에 넣어주는 함수 ---------------------------------------------------------
	size_t csize = GET_SIZE(HDRP(bp));								      // 헤더의 사이즈를 읽어옴

	if ((csize - asize) >= (2 * DSIZE)) {								  // 삽입하고 자리가 남으면 SPLIT 해준다.
		cut_link(bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));

		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		push_first(bp);

	}
	else {																  // 딱 맞는다면 그냥 넣어준다.
		cut_link(bp);
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}


void mm_free(void* bp)													  //블록 free시키는 함수 ---------------------------------------------------------------
{
	size_t size = GET_SIZE(HDRP(bp));									  // 헤더의 사이즈를 읽어옴

	PUT(HDRP(bp), PACK(size, 0));									      // 헤더에 free 입력
	PUT(FTRP(bp), PACK(size, 0));										  // 푸터에 free 입력

	coalesce(bp);														  // coalesce 시켜줌
}

static void cut_link(void* bp) { 									      //블록의 연결된 링크를 끊어버리는 함수 ------------------------------------------------
	if (PREV_FREE_BLKP(bp) != (char*)NULL) {
		CHANGE_NEXT(PREV_FREE_BLKP(bp), NEXT_FREE_BLKP(bp));			  // 전에 free의 next를 내 다음 free로
	}
	if (NEXT_FREE_BLKP(bp) != (char*)NULL) {
		CHANGE_PREV(NEXT_FREE_BLKP(bp), PREV_FREE_BLKP(bp));			  // 다음 free의 prev를 내 전 free로
	}
}


static void push_first(void* bp) {								          // free된 블록을 맨앞으로 보내는 함수 -------------------------------------------------

	char* seg;
	seg = seg_find(GET_SIZE(HDRP(bp)));//

	if (PREV_FREE_BLKP(seg) != (char*)NULL) {							  // free list가 존재한다면 
		CHANGE_NEXT(PREV_FREE_BLKP(seg), bp);							  // 그 free 블록에 나(bp)를 연결한다. 
	}
	PUT_P(PREVRP(bp), PREV_FREE_BLKP(seg));								  // 나의 이전은 기존의 root에 연결되 있던 블록
	PUT_P(NEXTRP(bp), seg);												  // 나의 다음은 root
	PUT_P(PREVRP(seg), bp);											      // root의 이전은 나(bp)
}

static void* coalesce(void* bp)											  // 연속된 free 처리--------------------------------------------------------------------
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));					  // 전에 블록이 alloc 인가
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));					  // 다음 블록이 alloc 인가
	size_t size = GET_SIZE(HDRP(bp));									  // 현재 노드의 사이즈

	if (prev_alloc && next_alloc) {										  // case 1 : 앞 뒤 다 alloc
		push_first(bp);
		return bp;														  // 그냥 리턴
	}
	else if (prev_alloc && !next_alloc) {								  // case 2 : 다음도 free
		cut_link(NEXT_BLKP(bp));

		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));							  // 다음 블록의 사이즈까지 합쳐서 free시킴
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

		push_first(bp);
	}
	else if (!prev_alloc && next_alloc) {								  // case 3 : 전꺼도 free
		cut_link(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp)));							  // 전의 사이즈까지 합쳐서 free시킴
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

		push_first(PREV_BLKP(bp));

		bp = PREV_BLKP(bp);
	}
	else {																  // case 4 : 앞 뒤 다 free 
		cut_link(NEXT_BLKP(bp));
		cut_link(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

		push_first(PREV_BLKP(bp));

		bp = PREV_BLKP(bp);
	}
	return bp;
}

void* mm_realloc(void* bp, size_t size) 								  // reallocation--------------------------------------------------------------------
{
	char* old_dp = bp;
	char* new_dp;

	size_t old_size = GET_SIZE(HDRP(old_dp));
	size_t old_next_size = GET_SIZE(HDRP(NEXT_BLKP(old_dp)));

	if (!GET_ALLOC(HDRP(NEXT_BLKP(old_dp))) && old_size + old_next_size >= size) {  // 만약 뒤에 free 블록이 있고, 지금과 합쳤을 때 필요한 size를 담을 수 있다면
		size_t asize;

		if (size == 0)															    // 만약 입력받은 사이즈가 0 이면 무시
			return NULL;

		if (size <= DSIZE)															// 만약 입력받은 사이즈가 dsize보다 작아도 최소 size로 생성
			asize = 2 * DSIZE;
		else
			asize = DSIZE * ((size + (DSIZE)+(DSIZE - 1)) / DSIZE);					// 8의 배수(Dsize)로 생성

		cut_link(NEXT_BLKP(old_dp));												// 뒤 free 블록의 링크를 끊어줌

		if ((old_size + old_next_size - asize) >= (2 * DSIZE)) {					// 삽입하고 자리가 남으면 SPLIT 해준다.
			PUT(HDRP(bp), PACK(asize, 1));
			PUT(FTRP(bp), PACK(asize, 1));

			new_dp = NEXT_BLKP(bp);
			PUT(HDRP(new_dp), PACK(old_size + old_next_size - asize, 0));
			PUT(FTRP(new_dp), PACK(old_size + old_next_size - asize, 0));
			push_first(new_dp);														// split한 블록은 맨앞으로

		}
		else {																		// 딱 맞는다면 그냥 넣어준다.
			PUT(HDRP(bp), PACK(old_size + old_next_size, 1));
			PUT(FTRP(bp), PACK(old_size + old_next_size, 1));
		}

		return bp;
	}
	else {
		size_t copySize;

		new_dp = mm_malloc(size);											  // 다른데다가 다시 할당 받기

		if (new_dp == NULL)													  // 실패하면 NULL 리턴
			return NULL;

		copySize = GET_SIZE(HDRP(old_dp));									  // 원래 블록의 사이즈
		if (size < copySize)												  // 요청한 사이즈가 작다면 작은사이즈로 카피
			copySize = size;
		memcpy(new_dp, old_dp, copySize);

		mm_free(old_dp);													  // 기존 사이즈는 삭제

		return new_dp;
	}

}