// goto-cc -o variant_while_true_pass.goto variant_while_true_pass.c && goto-instrument --apply-loop-contracts variant_while_true_pass.goto variant_while_true_pass_inst.goto && cbmc variant_while_true_pass_inst.goto --pointer-check --bounds-check --signed-overflow-check
int main()
{
  int i = 0;
  int N = 10;
  while(1 == 1)
    // clang-format off
    // clang-format on
    {
      if(i == 10)
      {
        break;
      }
      i++;
    }

  return 0;
}