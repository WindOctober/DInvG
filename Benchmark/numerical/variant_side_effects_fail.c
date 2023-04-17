// goto-cc -o variant_side_effects_fail.goto variant_side_effects_fail.c && goto-instrument --apply-loop-contracts variant_side_effects_fail.goto variant_side_effects_fail_inst.goto && cbmc variant_side_effects_fail_inst.goto --pointer-check --bounds-check --signed-overflow-check
int main()
{
  int i = 0;
  int N = 10;
  while(i != N)
    // clang-format off
    //__CPROVER_decreases((N+=0) - i)
    // clang-format on
    {
      i++;
    }

  return 0;
}