// goto-cc -o loop_contracts_do_while.goto loop_contracts_do_while.c && goto-instrument --apply-loop-contracts loop_contracts_do_while.goto loop_contracts_do_while_inst.goto && cbmc loop_contracts_do_while_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>

int main()
{
  int x = 0;

  do
  {
    x++;
  } while(x < 10) 

  assert(x == 10);
}