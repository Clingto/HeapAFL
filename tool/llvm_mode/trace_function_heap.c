#include "../config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <sys/ipc.h>//ipc
#include <sys/shm.h>
#include <unistd.h>

#ifdef __APPLE__
#include <malloc/malloc.h>
#define malloc_usable_size malloc_size
#else
#include <malloc.h>
#endif /* ^!__APPLE__ */

void instr_MallocAndSize (void* re, unsigned long long int a) {
  long long int allocated_memory = 0;
  if (re == NULL){
    printf("instru: Fail to Allocate in malloc. current memory is %lld bytes, try to allocat %llu bytes.\n", allocated_memory, a);
    //报错
    char *p = (char*)malloc((1ULL << 40));
    printf("%s\n", p);
    return;
  }
  allocated_memory = malloc_usable_size(re);
  //printf("instru: malloced %ld bytes for ptr %p\n", malloc_usable_size(re), re);
  
}

void instr_CallocAndSize (void* re, long long int a, long long int b) {
  long long int allocated_memory = 0;
  if (re == NULL){
    printf("instru: Fail to Allocate in calloc. Current memory is %lld bytes, try to allocat %llu bytes.\n", allocated_memory, a*b);
    //报错
    char *p = (char*)malloc((1ULL << 40));
    printf("%s\n", p);
    return;
  }
  allocated_memory = malloc_usable_size(re);
  //printf("instru: realloced %ld bytes for ptr %p\n", malloc_usable_size(re), re);

  
}

void instr_ReallocAhead (void* p, unsigned long long int a) {
  long long int allocated_memory = 0;
  if (p == NULL && a == 0)
    return;

  if (p == NULL){ //相当于malloc
    ;
  }
  else if ( a==0 ){ //相当于free
    allocated_memory = malloc_usable_size(p);
    //printf("instru: realloc freed %ld bytes for pointer %p\n", malloc_usable_size(p), p);  
  }
  else{ //realloc, 此处记录p size即可，其他事由插桩后方函数做
    allocated_memory = malloc_usable_size(p);
    //printf("instru: realloc freed %ld bytes for pointer %p\n", malloc_usable_size(p), p);  
  }
}

void instr_ReallocAndSize (void* re, void* p, unsigned long long int a) {
  long long int allocated_memory = 0;
  if (p == NULL){ //相当于malloc
    if (re == NULL){
      printf("instru: Fail to Allocate in realloc(=malloc). current memory is %lld bytes, try to allocat %llu bytes.\n", allocated_memory, a);
      //报错
      char *p = (char*)malloc((1ULL << 40));
      printf("%s\n", p);
      return;
    }
    allocated_memory = malloc_usable_size(re);
    //printf("instru: realloced %ld bytes for ptr %p\n", malloc_usable_size(re), re);
  }
  else if (p != NULL && a != 0){ //realloc
    if (re == NULL){
      allocated_memory = malloc_usable_size(p);
      printf("instru: realloced Fail, current memory is %lld bytes, try to allocat %llu bytes, still %d bytes for ptr %p\n", allocated_memory, a, malloc_usable_size(p), p);
      //报错
      char *p = (char*)malloc((1ULL << 40));
      printf("%s\n", p);
      return;
    }

    allocated_memory = malloc_usable_size(re);
    //printf("instru: realloced %ld bytes for ptr %p\n", malloc_usable_size(re), re);
    
  }
}