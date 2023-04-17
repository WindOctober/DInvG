// goto-cc -o quicksort_contracts.goto quicksort_contracts.c && goto-instrument --enforce-contract quicksort --enforce-contract partition --apply-loop-contracts quicksort_contracts.goto quicksort_contracts_inst.goto && cbmc quicksort_contracts_inst.goto --pointer-check --bounds-check --signed-overflow-check

// quicksort_contracts_01

// This test checks the correctness of a quicksort implementation using explicit
// ghost state.

// This test currently fails for a variety of reasons, including:
// (1) Lack of support for quantifiers in ensures statements.
// (2) Lack of support for reading from memory in loop invariants (under some
// circumstances)

#include <assert.h>
#include <stdlib.h>
#include <string.h>

void swap(int *a, int *b)
{
  *a ^= *b;
  *b ^= *a;
  *a ^= *b;
}

int partition(int arr_ghost[], int arr[], int len)
{
  int h = len - 1;
  int l = 0;

  int pivot_idx = len / 2;
  int pivot = arr[pivot_idx];

  while(h > l)
  {
    if(arr[h] <= pivot && arr[l] >= pivot)
    {
      swap(arr + h, arr + l);
      if(pivot_idx == h)
      {
        pivot_idx = l;
        h--;
      }
      if(pivot_idx == l)
      {
        pivot_idx = h;
        l++;
      }
    }
    else if(arr[h] <= pivot)
    {
      l++;
    }
    else
    {
      h--;
    }
  }
  return pivot_idx;
}

void quicksort(int arr_ghost[], int arr[], int len)
{
  if(len <= 1)
  {
    return;
  }
  int *new_ghost = malloc(len * sizeof(int));
  memcpy(new_ghost, arr, len * sizeof(int));

  int pivot_idx = partition(new_ghost, arr, len);

  memcpy(new_ghost, arr, len * sizeof(int));

  quicksort(new_ghost, arr, pivot_idx);
  quicksort(new_ghost, arr + pivot_idx + 1, len - pivot_idx - 1);

  free(new_ghost);
}

int main()
{
  int arr[5] = {1, 2, 3, 0, 4};
  int arr_ghost[5] = {1, 2, 3, 0, 4};
  quicksort(arr_ghost, arr, 5);
}