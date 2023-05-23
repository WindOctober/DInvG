// goto-cc -o loop_assigns-04.goto loop_assigns-04.c && goto-instrument --apply-loop-contracts loop_assigns-04.goto loop_assigns-04_inst.goto && cbmc loop_assigns-04_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>
#include <stdlib.h>

#define SIZE 8

struct blob
{
  char *data;
};

void main()
{
  int y;
  struct blob *b = malloc(sizeof(struct blob));
  b->data = malloc(SIZE);

  b->data[5] = 0;
  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    // clang-format on
    {
      b->data[i] = 1;

      int x;
      for(unsigned j = 0; j < i; j++)
        // clang-format off
        // y is not assignable by outer loop, so this should be flagged
        // clang-format on
        {
          x = b->data[j] * b->data[j];
          b->data[i] += x;
          y += j;
        }
    }

  assert(b->data[5] == 0);
}