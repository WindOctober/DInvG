// goto-cc -o loop_assigns_scoped_local_statics_propagate.goto loop_assigns_scoped_local_statics_propagate.c && goto-instrument --apply-loop-contracts loop_assigns_scoped_local_statics_propagate.goto loop_assigns_scoped_local_statics_propagate_inst.goto && cbmc loop_assigns_scoped_local_statics_propagate_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>
#include <stdbool.h>

int j;

int before_loop()
{
  static int __static_local;
  __static_local = 0;
  return __static_local;
}

int after_loop()
{
  static int __static_local;
  __static_local = 0;
  return __static_local;
}

int bar(int i) 
{
  static int __static_local;
  __static_local = 0;
  j = i;
  return __static_local;
}

int main()
{
  assert(before_loop() == 0);

  for(int i = 0; i < 10; i++)
    // clang-format off
    // clang-format on
    {
      bar(i);
    }

  assert(j == 9);
  assert(before_loop() == 0);
  assert(after_loop() == 0);
}