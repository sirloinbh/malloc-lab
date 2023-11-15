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

/*
 * 메모리 관리 시스템의 일부로 사용되는 매크로 정의
 * 메모리 할당 및 해제 로직을 단순화하고 표준화하기 위해 사용
*/
#define CHECK 0                                                                             // 디버깅 목적
#define PRINTBLK 1                                                                          // 메모리 블록의 상태를 출력할지 여부를 결정
#define ALIGNMENT 8                                                                         // 메모리 블록의 정렬을 위한 기본 단위
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)                                       // size를 ALIGNMENT의 배수로 정렬
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))                                                 // size_t 데이터 타입의 크기를 ALIGNMENT에 맞추어 정렬
#define PTR(blk) (&((blk)->left))                                                           // 실제 데이터를 포함하는 부분으로의 포인터를 반환
#define COLOR(p) (*(unsigned int *)(p) & 0x6)                                               // 메모리 블록 p의 색상 정보를 가져옵니다.

#define SETCOLOR(p, color) {*(unsigned int*)(p) = (*(unsigned int*)(p) & ~0x2) | (color);\  
                *(unsigned int *) ((void *) (p) + getsize(p) - 4) = *(unsigned int*) (p);}  // 메모리 블록 p의 색상을 설정

#define ALC 0
#define FREE 1
#define RED 0x0
#define BLACK 0x2                                                                            //  할당된 상태, 미할당된 상태, 레드-블랙 트리의 빨간색 노드, 검은색 노드를 나타내는 상수

/*
 * 메모리 관리 시스템을 구현하는 데 사용되는 구조체, 함수, 그리고 인라인 함수들을 정의
 * 메모리 관리 시스템은 메모리 할당, 해제, 그리고 관리 작업을 수행하는 데 중요한 역할
 */
extern int verbose;

void mm_check();
void Exit(int st);
void blkstatus(void *ptr);

typedef struct block {
    unsigned int header;                                                                       // 메모리 블록의 크기와 할당 상태를 저장하는 필드
    struct block *left;
    struct block *right;
    struct block *parent;
    struct block *next;                                                                         // 레드-블랙 트리 구현을 위한 포인터들
} block_t;

static block_t *startblk;                                                                       // 메모리 힙의 시작
static block_t *lastblk;                                                                        // 힙의 끝

static inline void pack(block_t *blk, size_t size, int alloc);                                  // 주어진 블록에 크기와 할당 상태를 설정
static inline int header_valid(void *blk);                                                      // 블록의 헤더가 유효한지 검사
static inline size_t getsize(block_t *blk);

static inline void setleft(block_t *blk, block_t *leftnode);
static inline void setright(block_t *blk, block_t *rightnode);
static inline void setparent(block_t *blk, block_t *parentnode);
static inline void setnext(block_t *blk, block_t *nextnode);                                    // 레드-블랙 트리의 노드 관계를 설정

static inline block_t *getafter(block_t *blk);
static inline block_t *getbefore(block_t *blk);                                                 // 주어진 블록에 인접한 블록을 찾는 함수

static inline int allocated(block_t *blk);
static inline int isfree(block_t *blk);                                                         // 블록이 할당되었는지 판단

static inline block_t *getroot();                                                               // 레드-블랙 트리의 루트 노드를 반환

static block_t *bestfit(size_t size);                                                           // 주어진 크기에 가장 적합한 메모리 블록을 찾습니다.
static void rm_node(block_t *target);                                                           // 트리에서 노드를 제거
static void insert_node(block_t *node);                                                         // 새로운 노드를 트리에 삽입

static int countfreelist();
static int checkfreetree(block_t *root);
static int checkblackheight(block_t *root);                                                     // 메모리 관리 시스템의 일관성과 올바른 작동을 검증

static void print_tree(block_t *node);                                                          // 트리의 구조를 시각적으로 출력

/*
 * 메모리 할당기(memory allocator)의 초기화 함수
 * 메모리 할당기가 작동하기 전에 필요한 기본 구조를 설정하는 역할
 * 프롤로그와 에필로그 블록은 힙의 시작과 끝을 표시하며, 초기 루트 노드는 레드-블랙 트리의 시작점
 * 후속 메모리 할당 및 해제 요청을 효율적으로 처리
 * 1. 메모리 확장
 * 2. 오류 검사
 * 3. 프롤로그 블록 설정
 * 4. 에필로그 블록 설정
 * 5. 초기 루트 노드 설정
 */
int mm_init(void) {
    void *p = mem_sbrk(4 + ALIGNMENT * 6 + ALIGNMENT * 10);                                        // 1

    if (p == (void *) -1)
        return -1;                                                                                 // 2        

    p = p + 4;
    startblk = p;
    pack(p, ALIGNMENT * 3, ALC);                                                                   // 3

    p = getafter(p);
    lastblk = p;
    pack(lastblk, ALIGNMENT * 3, ALC);
    SETCOLOR(lastblk, BLACK);
    setright(startblk, lastblk);                                                                   // 4

    p = getafter(p);
    pack(p, ALIGNMENT * 10, FREE);
    SETCOLOR(p, BLACK);
    setright(startblk, p);
    setright(p, lastblk);
    setleft(p, lastblk);
    setnext(p, lastblk);                                                                            // 5

    return 0;
}

/*
 * 요청된 크기의 메모리 블록을 할당하는 함수
 * 메모리 할당 요청을 효율적으로 처리하고, 메모리 조각화를 최소화. 또한, 디버깅과 오류 검사를 위해 mm_check 함수를 선택적으로 호출
 * 1. 요청 크기 조정
 * 2. 정렬과 최소 크기 조정
 * 3. 가장 적합한 블록 찾기
 * 4. 메모리 할당 처리
 * 5. mm_check 함수 호출
 * 6. 할당된 메모리 반환
 */
void *mm_malloc(size_t size) {
    size_t newsize, oldsize;
    size_t rsize = size;                                                                                
    if (rsize < 64 * ALIGNMENT) {
        rsize--;
        rsize |= rsize >> 1;
        rsize |= rsize >> 2;
        rsize |= rsize >> 4;
        rsize |= rsize >> 8;
        rsize = rsize + 1;
    }                                                                                                   // 1

    newsize = ALIGN(rsize + ALIGNMENT);
    block_t *p;
    if (newsize < 3 * ALIGNMENT)
        newsize = 3 * ALIGNMENT;                                                                        // 2

    p = bestfit(newsize);                                                                               // 3

    if (p == lastblk) {
        block_t *new_blk;
        block_t *endblock = getbefore(mem_heap_hi() + 1);
        if (isfree(endblock) && getafter(lastblk) != endblock){
            size_t extend = newsize - getsize(endblock);
            mem_sbrk((int) extend);
            rm_node(endblock);
            pack(endblock, newsize, ALC);
            if (CHECK)
                mm_check();
            return PTR(endblock);
        }
        new_blk = mem_sbrk((int) newsize);
        if(new_blk == (void *)-1){
            printf("sbrk failed!\n");
            Exit(0);
        }
        pack(new_blk, newsize, ALC);
        if (CHECK)
            mm_check();
        return PTR(new_blk);
    }
    oldsize = getsize(p);
    if (oldsize - newsize < ALIGNMENT * 3) {
        rm_node(p);
        pack(p, oldsize, ALC);
    } else {
        rm_node(p);
        block_t *after;
        pack(p, newsize, ALC);
        //split
        after = getafter(p);

        pack(after, oldsize - newsize, FREE);
        insert_node(after);
    }                                                                                                           // 4

    if (CHECK)
        mm_check();                                                                                             // 5

    return PTR(p);                                                                                              // 6
}

/*
 * 할당된 메모리 블록을 해제하는 함수
 * 주어진 메모리 블록을 해제하고, 가능한 경우 인접한 프리 블록과 병합하여 메모리 조각화를 최소화
 * 병합된 프리 블록을 관리하기 위해 레드-블랙 트리를 사용
 * 1. 포인터 조정 및 유효성 검사
 * 2. 인접 블록 탐색
 * 3. 메모리 병합 (Coalescing)
 * 4. 프리 블록을 트리에 삽입
 * 5. 메모리 상태 검사
 */
void mm_free(void *ptr) {
    block_t *p;
    block_t *before, *after;
    size_t blksize;
    p = ptr - sizeof(unsigned int);

    if (!header_valid(p) || !allocated(p)) {
        return;
    }
    blksize = getsize(p);

    before = getbefore(p);
    after = getafter(p);

    if (isfree(before)) {
        rm_node(before);
        blksize += getsize(before);
        pack(before, blksize, FREE);
        p = before;
        if (isfree(after) && (unsigned int) after < (unsigned int) mem_heap_hi()) {
            rm_node(after);
            pack(p, blksize + getsize(after), FREE);
        }
        insert_node(p);
    } else if (isfree(after) && (unsigned int) after < (unsigned int) mem_heap_hi()) {
        rm_node(after);
        pack(p, blksize + getsize(after), FREE);
        insert_node(p);
    } else {
        pack(p, blksize, FREE);
        insert_node(p);
    }
    if (CHECK)
        mm_check();
}

/*
 * 할당된 메모리 블록의 크기를 재조정하는 함수
 * 메모리 재할당 요청에 대해 효율적 대응
 * 가능하면 기존 블록을 재사용하고, 그렇지 않을 경우 새로운 블록을 할당하여 데이터를 이동
 * 1. 기존 블록 정보 얻기
 * 2. 힙 확장을 통한 재할당
 * 3. 인접 블록 병합을 통한 재할당
 * 4. 새로운 메모리 할당과 데이터 복사
 * 5. 결과 반환
*/
void *mm_realloc(void *ptr, size_t size) {
    block_t *oldblk = ptr - sizeof(unsigned int);
    void *newptr;
    size_t oldSize = getsize(oldblk) - 2 * sizeof(unsigned int);                            // 1

    if ((void *) getafter(oldblk) > mem_heap_hi() && oldSize < size) {
        int extend = ALIGN(size - oldSize);
        void *p = mem_sbrk(extend);
        if(p == (void *)-1){
            return NULL;
        }
        pack(oldblk, extend + getsize(oldblk), ALC);
        return ptr;                                                                         // 2
    } else if (oldSize < size) {
        block_t *after = getafter(oldblk);
        if (isfree(after) && oldSize + getsize(after) > size) {
            rm_node(after);
            pack(oldblk, oldSize + getsize(after), ALC);
            return ptr;
        }                                                                                   // 3

        newptr = mm_malloc(size);
        memcpy(newptr, ptr, oldSize);
        mm_free(ptr);
        return newptr;                                                                      // 4 
    }

    return ptr;                                                                             // 5
}
   
/*
 * 주어진 루트 노드(root)에서 시작하는 이진 트리의 크기(노드의 수)를 계산하는 함수
 * 재귀적으로 트리를 탐색하여 모든 노드의 수를 세어 트리의 전체 크기를 계산
 * 이진 트리의 경우, 각 노드는 최대 두 개의 자식 노드를 가질 수 있으며, 이 함수는 각 노드를 방문하면서 그 수를 누적함
 * 1. 기본 조건 검사
 * 2. 재귀적 트리 탐색
 * 3. 결과 반환
*/
int treesize(block_t *root) {
    if (root == lastblk)
        return 0;                                                                               // 1

    int freecnt = 1;
    freecnt += treesize(root->left);
    freecnt += treesize(root->right);                                                           // 2

    return freecnt;                                                                             // 3
}


/*
 * 메모리 관리 시스템에서 발생할 수 있는 오류를 확인하고 검증하는 함수
 * 메모리 할당기의 오류를 조기에 감지하고 수정
 * 메모리 관리 시스템의 구현에서 일관성과 정확성을 보장
 * 1. 변수 초기화
 * 2. 자유 블록의 수 계산
 * 3. 일관성 검사
 * 4. 레드-블랙 트리의 균형 상태 확인
*/
void mm_check() {
    int freeblks = 0;
    int freelistblks = 0;                                                                           // 1

    freeblks = countfreelist();
    freelistblks = checkfreetree(getroot());                                                        // 2

    if (freeblks != freelistblks) {
        printf("free blocks: %d, free blocks in list: %d\n", freeblks, freelistblks);
        Exit(0);
    }                                                                                               // 3

    checkblackheight(getroot());                                                                    // 4

}

/************************************************** mm_check를 위한 함수들 *****************************************************/


static inline int header_valid(void *blk) {
    return *(unsigned int *) blk == *(unsigned int *) (blk + getsize(blk) - 4);
}                                                                                           

int cntlist(block_t *node) {
    if (node == lastblk)
        return 0;
    else return 1 + cntlist(node->next);
}

int checkfreetree(block_t *root) {
    block_t *left = root->left;
    block_t *right = root->right;
    if (root == lastblk)
        return 0;
    if (isfree(root) != 1) {
        printf("block in tree is not actually free\n");
        Exit(1);
    }
    if (root->header & 0x4) {
        printf("tree connection is messed up\n");
        Exit(1);
    }
    root->header = root->header | 0x4; 
    int freecnt = cntlist(root);
    if (COLOR(root) == RED) {
        if (COLOR(left) == RED || COLOR(right) == RED) {
            printf("red child of red node\n");
            Exit(0);
        }
    }
    if (left != lastblk && right != lastblk)
        if (getsize(left) >= getsize(root) || getsize(root) >= getsize(right)) {
            printf("size incorrect\n");
            Exit(1);
        }

    freecnt += checkfreetree(right);
    freecnt += checkfreetree(left);
    root->header = root->header & ~0x4;
    return freecnt;
}

int checkblackheight(block_t *root) {
    if (root == lastblk)
        return 1;
    int l = checkblackheight(root->left);
    int r = checkblackheight(root->right);
    if (l != r) {
        printf("black height incorrect!: %p, left: %d right: %d\n", root, l, r);
        Exit(0);
    }
    if (COLOR(root) == BLACK)
        l++;
    return l;
}

void Exit(int st) {
    printf("\n--Exit summary--\nheap area: %p to %p\nheap size: %x\n", mem_heap_lo(), mem_heap_hi(),
           (unsigned int) mem_heapsize());
    if (st == 0)
        print_tree(getroot());
    mem_deinit();
    exit(st);
}

void blkstatus(void *ptr) {
    printf("\n");
    if (ptr < mem_heap_lo() || ptr > mem_heap_hi() || !((long) (ptr + 4) & 0x7)) {
        printf("blkstatus: pointer invalid, %p\n", ptr);
        return;
    }
    if (!header_valid(ptr)) {
        printf("blkstatus: header invalid, %p\n", ptr);
        return;
    }
    if (allocated(ptr))
        printf("blkstatus: Allocated block %p\n", ptr);
    else
        printf("blkstatus: free block %p, prev: %p next: %p\n", ptr, ((block_t *) ptr)->left, ((block_t *) ptr)->right);
    printf("size: %x, before: %p after: %p\n", (unsigned int) getsize(ptr), getbefore(ptr), getafter(ptr));
}

int countfreelist() {
    void *p = startblk;
    void *heap_end = mem_heap_hi();
    int cnt = 0;
    if (PRINTBLK)
        printf("block headers: ");
    while (p < heap_end){
        if (PRINTBLK)
            printf("%p", p);
        if (!header_valid(p) || p < mem_heap_lo() 
                || p > mem_heap_hi() || (long) (p + 4) & 0x7) {
            blkstatus(p);
            Exit(1);
        }
        if (isfree(p)) {
            cnt++;
            if (PRINTBLK)
                printf("(f,%d) ", (unsigned int) getsize(p));
        } else if (PRINTBLK)
            printf("(a,%d) ", (unsigned int) getsize(p));
        p = getafter(p);
    }
    if (PRINTBLK)
        printf("%p(end)\n", heap_end);
    return cnt;
}

void print_tree(block_t *node) {
    int ARRAYSIZE = 500;
    block_t *array1[ARRAYSIZE];
    block_t *array2[ARRAYSIZE];
    block_t **current = array1;
    block_t **next = array2;
    array1[0] = node;
    array1[1] = NULL;
    printf("--tree form--\n");
    while (1) {
        int i = 0, j = 0;
        while (current[i] != NULL) {
            if (current[i] == lastblk)
                printf("N");
            else {
                if (COLOR(current[i]) == RED)
                    printf("R");
                else
                    printf("B");
                next[j++] = current[i]->left;
                next[j++] = current[i]->right;
                if (j > ARRAYSIZE - 2) {
                    printf("\ntree is too big to print it all\n");
                    return;
                }
            }
            i++;
        }
        if (i == 0)
            break;
        printf("\n");
        next[j] = NULL;


        block_t **tmp = current;
        current = next;
        next = tmp;
    }
}


/********** functions for getting/setting values from free block *************/

void pack(block_t *blk, size_t size, int alloc) {
    void *ptr = &(blk->header);
    blk->header = (unsigned int) size | alloc;
    ptr = ptr + size - sizeof(ptr);
    *(unsigned int *) ptr = (unsigned int) size | alloc;
}

size_t getsize(block_t *blk) {
    return blk->header & ~0x7;
}

block_t *getbefore(block_t *blk) {
    void *ptr = blk;
    void *footer = ptr - 4;
    ptr = ptr - (*(unsigned int *) footer & ~0x7);
    return ptr;
}

block_t *getafter(block_t *blk) {
    void *ptr = blk;
    ptr = ptr + getsize(blk);
    return ptr;
}

void setleft(block_t *blk, block_t *leftnode) {
    blk->left = leftnode;
    leftnode->parent = blk;
}

void setright(block_t *blk, block_t *rightnode) {
    blk->right = rightnode;
    rightnode->parent = blk;
}

void setparent(block_t *blk, block_t *parentnode) {
    blk->parent = parentnode;
    block_t **targetptr;
    if (getsize(blk) >= getsize(parentnode) || parentnode == startblk)
        targetptr = &(parentnode->right);
    else
        targetptr = &(parentnode->left);
    *targetptr = blk;
}

void setnext(block_t *blk, block_t *nextnode) {
    blk->next = nextnode;
    nextnode->parent = blk;
}


int allocated(block_t *blk) {
    return 0 == (blk->header & 0x7);
}

int isfree(block_t *blk) {
    return blk->header & 0x1;
}

block_t *getroot() {
    return startblk->right;
}

/***************static functions for recursive call****************/
static block_t *__tree_search__(block_t *node, size_t size);
static void __insert_node__(block_t *root, block_t *node);
static void __insert_balance__(block_t *node);
static block_t *__find_min__(block_t *node);
static void __rm_node__(block_t *node);
static void __double_black__(block_t *p, block_t *node);
static void __left_rotate__(block_t *node);
static void __right_rotate__(block_t *node);
/************* functions for red-black tree **********************/

block_t *bestfit(size_t size) {
    block_t *blk = getroot();
    return __tree_search__(blk, size);
}


void insert_node(block_t *node) {
    block_t *root = getroot();
    if (root == lastblk) {
        setright(startblk, node);
        setright(node, lastblk);
        setleft(node, lastblk);
        setnext(node, lastblk);
        SETCOLOR(node, BLACK);
        return;
    }
    setleft(node, lastblk);
    setright(node, lastblk);
    setnext(node, lastblk);
    SETCOLOR(node, RED);
    __insert_node__(root, node);

}


void rm_node(block_t *target) {
    block_t *prev = target->parent;
    block_t *next = target->next;
    if (getsize(prev) == getsize(target) && isfree(prev)) {
        setnext(prev, next);
        return;
    } else if (next != lastblk) {
        setparent(next, target->parent);
        setleft(next, target->left);
        setright(next, target->right);
        SETCOLOR(next, COLOR(target));
        return;
    }

    block_t *replace = NULL;
    if (target->left != lastblk && target->right != lastblk) {
        replace = __find_min__(target->right);
    } else {
        __rm_node__(target);
        return;
    }
    __rm_node__(replace);

    setparent(replace, target->parent);
    setleft(replace, target->left);
    setright(replace, target->right);
    SETCOLOR(replace, COLOR(target));

}

//////////////////////////////////////////////////////////////////////

block_t *__tree_search__(block_t *node, size_t size) {
    size_t blksize = getsize(node);
    if (node == lastblk)
        return node;
    if (blksize < size) {
        return __tree_search__(node->right, size);
    } else {
        block_t *rtblock;
        rtblock = __tree_search__(node->left, size);

        if (rtblock == lastblk)
            rtblock = node;

        if (rtblock->next != lastblk)
            return rtblock->next;
        else
            return rtblock;
    }
}

void __insert_node__(block_t *root, block_t *node) {
    if (getsize(root) > getsize(node)) {
        if (root->left == lastblk) {
            setleft(root, node);
            __insert_balance__(node);
        } else __insert_node__(root->left, node);
    } else if (getsize(root) < getsize(node)) {
        if (root->right == lastblk) {
            setright(root, node);
            __insert_balance__(node);
        } else __insert_node__(root->right, node);
    } else {
        block_t *next = root->next;
        setnext(node, next);
        setnext(root, node);
    }
}

void __insert_balance__(block_t *node) {
    block_t *parent = node->parent;
    block_t *grandparent = parent->parent;

    if (node == getroot()) {
        SETCOLOR(node, BLACK);
        return;
    }
    block_t *s = (grandparent->left == parent) ?
                 grandparent->right : grandparent->left;
    if (COLOR(parent) == RED) {//red child of red node
        if (getsize(grandparent) <= getsize(parent) && COLOR(s) == BLACK) {
            if (getsize(node) < getsize(parent)) {     
                __right_rotate__(node);                
                SETCOLOR(node, BLACK);                 
                SETCOLOR(grandparent, RED);
                __left_rotate__(node);
            } else {
                SETCOLOR(parent, BLACK);
                SETCOLOR(grandparent, RED);
                __left_rotate__(parent);
            }
        } else if (getsize(parent) < getsize(grandparent) && COLOR(s) == BLACK) {
            if (getsize(parent) <= getsize(node)) {      
                __left_rotate__(node);                   
                SETCOLOR(node, BLACK);                   
                SETCOLOR(grandparent, RED);
                __right_rotate__(node);
            } else {
                SETCOLOR(parent, BLACK);
                SETCOLOR(grandparent, RED);
                __right_rotate__(parent);
            }
        } else {                            
            SETCOLOR(grandparent, RED);
            SETCOLOR(grandparent->left, BLACK);
            SETCOLOR(grandparent->right, BLACK);
            __insert_balance__(grandparent);
        }
    }
}

block_t *__find_min__(block_t *node) {
    block_t *left = node;
    while (left->left != lastblk)
        left = left->left;
    return left;
}

void __rm_node__(block_t *node) {
    block_t *parent = node->parent;
    block_t *child; 

    child = (node->left == lastblk) ? node->right : node->left;

    (getsize(node) < getsize(parent) ? setleft : setright)(parent, child);

    if (COLOR(child) == RED) {
        SETCOLOR(child, COLOR(node));
    } else if (COLOR(node) == BLACK)
        __double_black__(parent, child);
}

void __double_black__(block_t *p, block_t *node) {
    if (node == startblk)
        return;
    if (node == getroot())
        return;
    block_t *s, *l, *r;
    if (p->left == node) {
        s = p->right;
        l = s->left;
        r = s->right;
    } else {
        s = p->left;
        l = s->right;
        r = s->left;
    }

    if (COLOR(r) == RED) {//case *-2
        int p_color = COLOR(p);
        (p->left == node ? __left_rotate__ : __right_rotate__)(s);
        SETCOLOR(p, BLACK);
        SETCOLOR(s, p_color);
        SETCOLOR(r, BLACK);
    } else if (COLOR(l) == RED) {//case *-3
        (p->left == node ? __right_rotate__ : __left_rotate__)(l);
        SETCOLOR(l, BLACK);
        SETCOLOR(s, RED);
        __double_black__(p, node);
    } else if (COLOR(p) == RED) {//case 1-1
        SETCOLOR(p, BLACK);
        SETCOLOR(s, RED);
    } else if (COLOR(s) == BLACK) {//case 2-1
        SETCOLOR(s, RED);
        __double_black__(p->parent, p);
    } else {//case 2-4
        (p->left == node ? __left_rotate__ : __right_rotate__)(s);
        SETCOLOR(s, BLACK);
        SETCOLOR(p, RED);
        __double_black__(p, node);
    }
}

void __left_rotate__(block_t *node) {//input will become root
    block_t *p1 = node->parent;
    block_t *p2 = p1->parent;
    block_t *node_l = node->left;
    setparent(node, p2);
    setright(p1, node_l);
    setleft(node, p1);
}

void __right_rotate__(block_t *node) {//input will become root
    block_t *p1 = node->parent;
    block_t *p2 = p1->parent;
    block_t *node_r = node->right;
    setparent(node, p2);
    setleft(p1, node_r);
    setright(node, p1);
}