// goto-cc -o loop_assigns-05.goto loop_assigns-05.c && goto-instrument --apply-loop-contracts loop_assigns-05.goto loop_assigns-05_inst.goto && cbmc loop_assigns-05_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>

int j;

int lowerbound()
{
  return 0;
}

int upperbound()
{
  return 10;
}

void incr(int *i)
{
  (*i)++;
}

void body_1(int i)
{
  j = i;
}

void body_2(int *i)
{
  (*i)++;
  (*i)--;
}

int body_3(int *i)
{
  (*i)++;
  if(*i == 4)
    return 1;

  (*i)--;
  return 0;
}

int main()
{
  for(int i = lowerbound(); i < upperbound(); incr(&i))
    // clang-format off

    // clang-format on
    {
      body_1(i);

      if(body_3(&i))
        return 1;

      body_2(&i);
    }

  assert(j == 9);
}