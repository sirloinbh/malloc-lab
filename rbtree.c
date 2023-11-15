#include "rbtree.h"

#include <stdlib.h>


//새로운 레드-블랙 트리를 생성하고 초기화 하는 함수.
rbtree *new_rbtree(void) {

  // rbtree 구조체에 대한 메모리를 할당
  rbtree *new = (rbtree *)calloc(1, sizeof(rbtree));
  if(new == NULL){
    return NULL;
  }

  // 'nil'노드를 위한 메모리를 할당
  node_t *nil = (node_t *)calloc(1, sizeof(node_t));
  if(nil == NULL){
    free(new);
    return NULL;
  }
  
  // 'nil' 노드의 색을 검은색으로 변경
  nil->color = RBTREE_BLACK;

  // 트리 초기화
  new->root = nil;
  new->nil = nil;
  return new;
}

//재귀적으로 노드를 해제하는 보조 함수
void free_rbtree_nodes(node_t *node, node_t *nil) {

  //nil 노드에 도달 시 반환
  if(node == nil){
    return;
  }

  //왼쪽 서브 트리를 재귀적으로 해제
  free_rbtree_nodes(node->left, nil);

  //오른쪽 서브 트리를 재귀적으로 해제
  free_rbtree_nodes(node->right, nil);

  //현재 노드를 해제
  free(node);
}

//RB 트리를 해제 하는 함수
void delete_rbtree(rbtree *t) {

  //루트 노드가 nil노드가 아니라면 모든 노드의 메모리를 해제
  if (t->root != t->nil){
    free_rbtree_nodes(t->root, t->nil);
  }

  //nil 노드에 할당된 메모리를 해제
  free(t->nil);

  //RB 트리 구조체에 할당된 메모리를 해제
  free(t);
}

//왼쪽으로 회전하는 함수
void left_rotate(rbtree *t, node_t *node){
  //node의 오른쪽 자식으로 right_child를 선언하고 초기화
  node_t *right_child = node->right;

  //right_child의 왼쪽 서브 트리를 node의 오른쪽 서브 트리로 이동
  node->right = right_child->left;
  
  //y의 왼쪽 서브트리가 nil이 아니면, 그 부모를 node로 설정
  if(right_child->left != t->nil){
    right_child->left->parent = node;
  }

  //right_child의 부모를 node의 부모로 설정
  right_child->parent = node->parent;

  //node가 루트면 루트를 right_child로 설정
  if(node->parent == t->nil){
    t->root = right_child;
  } 
  //node가 부모의 왼쪽 자식이면 그것을 right_child로 설정
  else if ( node == node->parent->left){
    node->parent->left = right_child;
  } 
  //node가 부모의 오른쪽 자식이면 그것을 right_child로 설정
  else {
    node->parent->right = right_child;
  }

  //right_child의 왼쪽 자식을 node로 설정, node의 부모를 right_child로 설정
  right_child->left = node;
  node->parent = right_child;

}

//오른쪽으로 회전하는 함수
void right_rotate(rbtree *t, node_t *node){
  //왼쪽으로 회전하는 함수와 대칭적으로 동일
  node_t *right_child = node-> left;

  node->left = right_child->right;
  
  if(right_child->right != t->nil){
    right_child->right->parent = node;
  }

  right_child->parent = node->parent;

  if(node->parent == t->nil){
    t->root = right_child;
  } 
  else if ( node == node->parent->right){
    node->parent->right = right_child;
  } 
  else {
    node->parent->left = right_child;
  }

  right_child->right = node;
  node->parent = right_child;
}

//RB 트리에 새 노드를 삽입 시 RB의 속성에 맞게 고치는 함수
void rbtree_insert_fixup(rbtree *t, node_t *z) {
  node_t *y = NULL;

  // z의 부모가 레드인 동안 루프를 수행합니다.
  while(z->parent->color == RBTREE_RED){
     // z의 부모가 왼쪽 자식일 경우
    if(z->parent == z->parent->parent->left){
      // y를 z의 삼촌 노드로 설정
      y = z->parent->parent->right;
      // 삼촌 노드가 레드일 경우, 부모를 블랙으로, 삼촌을 블랙으로, 조부모를 레드로 변경
      if(y->color == RBTREE_RED){
        z->parent->color = RBTREE_BLACK;
        y->color = RBTREE_BLACK;
        z->parent->parent->color = RBTREE_RED;
        z = z->parent->parent;
      }
      //삼촌 노드가 블랙일 경우
      else {
        //z가 오른쪽 자식이면 부모노드로 이동 후 왼쪽 회전
        if(z == z->parent->right){
          z = z->parent;
          left_rotate(t,z);
        }
        //z가 왼쪽 자식이면 부모를 블랙으로, 조부모를 레드로 변경 후 오른쪽 회전
        z->parent->color = RBTREE_BLACK;
        z->parent->parent->color = RBTREE_RED;
        right_rotate(t, z->parent->parent);
      }
    }
    //z의 부모가 오른쪽 자식일 경우는 대칭적으로 동일
    else{
      y = z->parent->parent->left;
      if(y->color == RBTREE_RED){
        z->parent->color = RBTREE_BLACK;
        y->color = RBTREE_BLACK;
        z->parent->parent->color = RBTREE_RED;
        z = z->parent->parent;
      }
      else {
        if(z == z->parent->left){
          z = z->parent;
          right_rotate(t, z);
        }
        z->parent->color = RBTREE_BLACK;
        z->parent->parent->color = RBTREE_RED;
        left_rotate(t,z->parent->parent);
      }
    }
  }
  //루트 노드를 블랙으로 변경
  t->root->color = RBTREE_BLACK;
}

//새 키를 RB트리에 삽입하는 함수
node_t *rbtree_insert(rbtree *t, const key_t key) {

  //y는 삽입될 위치를 찾는 포인터, x는 탐색을 수행하는 포인터
  node_t *y = t->nil;
  node_t *x = t->root;

  // 새로 삽입될 노드 z의 메모리를 할당
  node_t *z = (node_t *)malloc(sizeof(node_t));
  if(z == NULL){
    return NULL;
  }
  
  // z 노드의 속성: 빨강색, 자식 노드는 nil노드, 매개변수 키를 키값으로 가진다.
  z->color = RBTREE_RED;
  z->left = t->nil;
  z->right = t->nil;
  z->key = key;

  //트리를 내려가면서 새 노드의 삽입 위치를 찾는다.
  while(x != t->nil){
    y = x;
    //현재 노드의 키를 비교해서 새 키가 작으면 왼쪽, 크거나 같으면 오른쪽 노드로 이동
    if(z->key < x->key){
      x = x->left;
    }
    else x = x->right;
  }
  //y를 z의 부모 노드로 변경
  z->parent = y;

  //z를 연결
  if(y == t->nil){
    t->root = z;
  }
  else if(z->key < y->key){
    y->left = z;
  }
  else y->right = z;

  //새로 삽입된 노드에 대해서 조정작업을 수행한 후 반환
  rbtree_insert_fixup(t,z);
  return z;
}

//rb트리에서 주어진 키값을 가진 노드를 찾는 함수
node_t *rbtree_find(const rbtree *t, const key_t key) {
  //현재 노드를 루트 노드로 설정
  node_t *current = t->root;

  //현재 노드가 nil노드가 되기 전 까지 탐색. 
  while(current != t->nil){
    //현재 노드의 키와 매개변수 키가 동일하면 현재 노드를 반환
    if(current->key == key){
      return current;
    }
    //현재 노드의 키가 매개변수의 키보다 작으면 오른쪽 자식노드로 이동
    else if(current->key < key){
      current = current->right;
    }
    //현재 노드의 키가 매개변수의 키보다 크면 왼쪽 자식노드로 이동
    else current = current->left;
  }
  //미발견
  return NULL;
}

//RB트리의 최소값을 찾는 함수
node_t *rbtree_min(const rbtree *t) {
  node_t *current = t->root;

  //현재 트리가 비었을 경우 못찾았음을 리턴
  if (current == t->nil){
    return NULL;
  }
  //nil 노드를 만나기 전까지 왼쪽 자식 노드들로 이동 후 리턴
  while(current->left != t->nil){
    current = current->left;
  }
  return current;
}

//RB트리의 최대값을 찾는 함수
node_t *rbtree_max(const rbtree *t) {
    node_t *current = t->root;

  //현재 트리가 비었을 경우 못찾았음을 리턴
  if (current == t->nil){
    return NULL;
  }
  //nil 노드를 만나기 전까지 오른쪽 자식 노드들로 이동 후 리턴
  while(current->right != t->nil){
    current = current->right;
  }
  return current;
}

//노드를 삭제 시 RB 트리를 고치는 함수
void rbtree_delete_fixup(rbtree *t, node_t *x) {
  //삭제하려는 노드가 루트노드가 아니고, 색이 검은색일경우
  while(x != t->root && x->color == RBTREE_BLACK){
    //삭제하려는 노드가 부모 노드의 왼쪽 노드일 경우
    if (x == x->parent->left){
      //형제 노드를 생성
      node_t *w = x->parent->right;

      //case 1: 형제노드가 빨강색인 경우 형제 노드를 검은색, 부모노드를 빨강색으로 변경 후 왼쪽 회전
      if (w->color == RBTREE_RED){
        w->color = RBTREE_BLACK;
        x->parent->color = RBTREE_RED;
        left_rotate(t,x->parent);
        w = x->parent->right;
      }

      //case 2: 형제 노드의 자식 노드 둘 다 검은색일 경우 
      if (w->left->color == RBTREE_BLACK  && w->right->color == RBTREE_BLACK){
        //형제 노드의 색을 빨강색으로 변경
        w->color =RBTREE_RED;
        //삭제하려는 노드에 부모노드를 대입
        x = x->parent;
      } else {
        // Case 3: 형제 노드의 오른쪽 자식만 블랙인 경우 형제 노드의 왼쪽 자식을 블랙, 형제 노드를 레드로 설정한 후 오른쪽 회전
        if(w->right->color == RBTREE_BLACK) {
          w->left->color = RBTREE_BLACK;
          w->color = RBTREE_RED;
          right_rotate(t,w);
          w = x->parent->right;
        }

        //case 4: 형제 노드의 색이 검은색이고 형제 노드의 오른쪽 자식이 레드일 경우 노드들의 색을 변경하고 왼쪽 회전
        w->color = x->parent->color;
        x->parent->color = RBTREE_BLACK;
        w->right->color = RBTREE_BLACK;
        left_rotate(t, x->parent);
        x = t->root;
      } 
    } else {
    //삭제하려는 노드가 부모 노드의 오른쪽 노드일 경우 대칭적으로 동일
      node_t *w = x->parent->left;

      //case 1
      if (w->color == RBTREE_RED){
        w->color = RBTREE_BLACK;
        x->parent->color = RBTREE_RED;
        right_rotate(t,x->parent);
        w = x->parent->left;
      }

      //case 2
      if(w->left->color == RBTREE_BLACK  && w->right->color == RBTREE_BLACK){
        w->color = RBTREE_RED;
        x = x->parent;
      }
      //case3
      else {
        if(w->left->color == RBTREE_BLACK) {
          w->right->color = RBTREE_BLACK;
          w->color = RBTREE_RED;
          left_rotate(t, w);
          w = x->parent->left;
        }

        //case 4
        w->color = x->parent->color;
        x->parent->color =RBTREE_BLACK;
        w->left->color =RBTREE_BLACK;
        right_rotate(t, x->parent);
        x = t->root;
      } 
    }
  }
  //삭제하려는 노드의 색을 검은색으로 설정
  x->color = RBTREE_BLACK;
}
//삭제 시 후계자 노드의 자리 변경 함수
void rb_transplant(rbtree *t, node_t *u, node_t *v) {
  //삭제한 노드가 루트 노드일 때 후계자 노드를 루트노드로 변경
  if (u->parent == t->nil) {
    t->root = v;
  //삭제한 노드의 자리를 후계자 노드로 대체
  } else if (u == u->parent->left) {
    u->parent->left = v;
  } else {
    u->parent->right = v;
  }
  v->parent = u->parent;
}

//서브트리의 노드들 중 키가 최소값을 가지는 노드를 반환하는 함수
node_t *rbtree_sub_min(const rbtree *t, node_t *subroot) {
  if (subroot == NULL) {
    return NULL;
  }

  //cursor는 현재 서브 루트, 왼쪽 자식으로 계속 이동
  node_t *cursor = subroot;
  while (cursor->left != t->nil) {
    cursor = cursor->left;
  }

  return cursor;
}

int rbtree_erase(rbtree *t, node_t *p) {
  //삭제하려는 노드의 후계자 노드를 생성
  node_t *y = p;
  color_t succeed_original_color = y->color;
  node_t *x;

  //삭제하려는 노드에게 왼쪽 자식이 없으면 오른쪽 자식이 후계자
  if(p->left == t->nil){
    x = p->right;
    rb_transplant(t,p, p->right);
  }
  //삭제하려는 노드에게 오른쪽 자식이 없으면 왼쪽 자식이 후계자
  else if(p->right == t->nil){
    x = p->left;
    rb_transplant(t,p, p->left);
  }
  //삭제하려는 노드에게 자식이 없으면 가장 가깝게 큰 수를 키로 가지는 노드가 후계자
  else{
    y = rbtree_sub_min(t,p->right);
    succeed_original_color = y->color;
    x = y->right;

    //
    if(y->parent == p){
      x->parent = y;
    } else {
      rb_transplant(t,y,y->right);
      y->right = p->right;
      y->right->parent = y;
    }
    //후계자 노드의 위치를 삭제된 노드 p의 위치로 옮김
    rb_transplant(t,p,y);
    y->left = p->left;
    y->left->parent = y;
    y->color = p->color;
  }
  if(succeed_original_color == RBTREE_BLACK){
    rbtree_delete_fixup(t,x);
  }

  free(p);
  return 0;
}
//재귀적으로 중위순회해서 키를 배열에 저장하는 함수
int recursive_inorder(const rbtree *t, node_t *node , key_t *arr, int *index){

  //nil노드가 아닐때만 중위순회
  if(node != t->nil){
    //왼쪽 서브 트리를 재귀적으로 중위순회
    recursive_inorder(t, node->left, arr, index);

    //현재 노드의 키를 배열에 삽입 후 인덱스 증가
    arr[*index] = node->key;
    (*index)++;

    //오른쪽 서브 트리를 재귀적으로 중위순회
    recursive_inorder(t, node->right, arr, index);
  }
  return 0;
}

//레드-블랙 트리를 배열로 변환하는 함수
int rbtree_to_array(const rbtree *t, key_t *arr, const size_t n) {
  
  // 빈 트리나 빈 배열이 주어진 경우 오류
  if(t == NULL || arr == NULL){
    return NULL;
  }

  //index 0을 가진 root노드부터 중위순회하여 배열에 저장
  int index = 0;
  recursive_inorder(t, t->root, arr, &index);

  //입력받은 배열의 크기가 트리보다 큰 경우 오류
  if((size_t)index > n){
    return NULL;
  }
  return 0;
}