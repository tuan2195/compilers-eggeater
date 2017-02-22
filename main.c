#include <stdio.h>
#include <stdlib.h>

extern int our_code_starts_here() asm("our_code_starts_here");
extern void error(int err_code) asm("error");
extern int print(int val) asm("print");

const int NUM_TAG    = 0x00000001;
const int BOOL_TRUE  = 0xFFFFFFFF;
const int BOOL_FALSE = 0x7FFFFFFF;

const int ERR_COMP_NOT_NUM   = 1;
const int ERR_ARITH_NOT_NUM  = 2;
const int ERR_LOGIC_NOT_BOOL = 3;
const int ERR_IF_NOT_BOOL    = 4;
const int ERR_OVERFLOW       = 5;

void printHelp(int val) {
  if((val & NUM_TAG) == 0x0)
  {
    printf("%d", val >> 1);
  }
  else if(val == BOOL_TRUE)
  {
    printf("true");
  }
  else if(val == BOOL_FALSE)
  {
    printf("false");
  }
  else if((val & 0x7) == 0x1)
  {
    int* arr = (int*)(val-1);
    int size = *arr;
    printf("(");
    for (int i = 1; i <= size; ++i)
    {
        printHelp(arr[i]);
        printf(i == size ? "" : ", ");
    }
    printf(")");
  }
}

int print(int val) {
  printHelp(val);
  printf("\n");
  return val;
}

void error(int i) {
  switch (i) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number");
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number");
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error logic expected a boolean");
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean");
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow");
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %d\n", i);
  }
  exit(i);
}

int main(int argc, char** argv) {
  int* HEAP = calloc(100000, sizeof (int));

  int result = our_code_starts_here(HEAP);
  print(result);
  return 0;
}

