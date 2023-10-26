// goto-cc -o variant_multidimensional_two_index_variables.goto variant_multidimensional_two_index_variables.c && goto-instrument --apply-loop-contracts variant_multidimensional_two_index_variables.goto variant_multidimensional_two_index_variables_inst.goto && cbmc variant_multidimensional_two_index_variables_inst.goto --pointer-check --bounds-check --signed-overflow-check
int main()
{
  int i = 0;
  int j = 0;
  int N = 10;
  while(i < N)
    // clang-format off

    // clang-format on
    {
      if(j < N)
      {
        j++;
      }
      else
      {
        i++;
        j = 0;
      }
    }
}