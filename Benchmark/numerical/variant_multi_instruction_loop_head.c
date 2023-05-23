// goto-cc -o variant_multi_instruction_loop_head.goto variant_multi_instruction_loop_head.c && goto-instrument --apply-loop-contracts variant_multi_instruction_loop_head.goto variant_multi_instruction_loop_head_inst.goto && cbmc variant_multi_instruction_loop_head_inst.goto --pointer-check --bounds-check --signed-overflow-check
int main()
{
  int x = 0;
  int *y = &x;

  while(*y <= 0 && *y < 10)
    // clang-format off
    // clang-format on
    {
      x++;
    }
}