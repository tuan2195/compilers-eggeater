#include <stdio.h>
#include <stdlib.h>

extern int our_code_starts_here() asm("our_code_starts_here");
extern void error(int err_code) asm("error");
extern int print(int val) asm("print");
extern int input() asm("input");
extern int equal(int a, int b) asm("equal");

const int NUM_TAG    = 0x00000001;
const int TUPLE_TAG  = 0x00000007;
const int BOOL_TRUE  = 0xFFFFFFFF;
const int BOOL_FALSE = 0x7FFFFFFF;

const int ERR_COMP_NOT_NUM   = 1;
const int ERR_ARITH_NOT_NUM  = 2;
const int ERR_LOGIC_NOT_BOOL = 3;
const int ERR_IF_NOT_BOOL    = 4;
const int ERR_OVERFLOW       = 5;
const int ERR_NOT_TUPLE      = 6;
const int ERR_INDEX_NOT_NUM  = 7;
const int ERR_INDEX_LARGE    = 8;
const int ERR_INDEX_SMALL    = 9;

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
  else if((val & TUPLE_TAG) == 0x1)
  {
    /*printf("val = %p\n", val);*/
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

int equal(int a, int b)
{
    if (a == b)
        return BOOL_TRUE;

    if (((a & TUPLE_TAG) != 0x1) || ((b & TUPLE_TAG) != 0x1))
        return BOOL_FALSE;

    const int* tup_a = (int*)(a - 1);
    const int* tup_b = (int*)(b - 1);

    for (size_t i = 0; i <= tup_a[0]; ++i)
        if (equal(tup_a[i], tup_b[i]) == BOOL_FALSE)
            return BOOL_FALSE;

    return BOOL_TRUE;
}

int inputHelp(char* input) {
  if (!input || input[0] == 'f') {
    return BOOL_FALSE;
  } else if (input[0] == 't') {
    return BOOL_TRUE;
  } else {
    return atoi(input) << 1;
  }
}

int input() {
  char in[80];
  scanf("%s", in);
  return inputHelp(in);
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
    fprintf(stderr, "Error: logic expected a boolean");
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean");
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: integer overflow");
    break;
  case ERR_NOT_TUPLE:
    fprintf(stderr, "Error: index operator expects a tuple");
    break;
  case ERR_INDEX_NOT_NUM:
    fprintf(stderr, "Error: index operator expects a number");
    break;
  case ERR_INDEX_LARGE:
    fprintf(stderr, "Error: index out of bounds - too large");
    break;
  case ERR_INDEX_SMALL:
    fprintf(stderr, "Error: index out of bounds - too small");
    break;
  default:
    fprintf(stderr, "Error: unknown error code: %d\n", i);
  }
  exit(i);
}

int main(int argc, char** argv) {
  int* HEAP = calloc(100000, sizeof (int));

  int result = our_code_starts_here(HEAP);
  print(result);
  return 0;
}

