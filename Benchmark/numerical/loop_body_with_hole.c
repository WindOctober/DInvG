// goto-cc -o loop_body_with_hole.goto loop_body_with_hole.c && goto-instrument --apply-loop-contracts loop_body_with_hole.goto loop_body_with_hole_inst.goto && cbmc loop_body_with_hole_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>
#include <stdbool.h>

int main()
{
  unsigned n, k, sum_to_k = 0;
  bool flag = false;

  for(unsigned i = 0; i < n; ++i)
    // clang-format off
    // clang-format on
    {
      if(i == k)
      {
        flag = true;
        break;
      }
      sum_to_k += i;
    }
}