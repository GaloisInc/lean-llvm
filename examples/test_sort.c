// An example program which merge sorts a static array

#include <stdio.h>
#include <stdint.h>

#define NELEMS 10

// for i in `seq 1 10`; do echo ${RANDOM},; done
uint64_t arr[NELEMS] = {
    20307,
    3714,
    12422,
    16382,
    29230,
    18967,
    22962,
    27145,
    12275,
    4617
};


// [low .. high]
unsigned int
partition(unsigned int low, unsigned int high)
{
    uint64_t pivot = arr[low];
    unsigned int frontier = low;

    for(unsigned int i = low + 1; i <= high; i++) {
        uint64_t v = arr[i];
        if (v < pivot) {
            frontier++;
            arr[i] = arr[frontier];
            arr[frontier] = v;
        }
    }
    
    arr[low] = arr[frontier];
    arr[frontier] = pivot;
    
    return frontier;
}

void
quicksort(unsigned int low, unsigned int high)
{
    if (low < high) {
        unsigned int pivot_idx = partition(low, high);
        quicksort(low, pivot_idx - 1);
        quicksort(pivot_idx + 1, high);
    }
}

static char digits[] = "0123456789abcdef";


void
write_hex_number_to_stdout(uint64_t num)
{
    for(int i = 15; i >= 0; i--)
        putchar(digits[(num >> i * 4) & 0xf]);

    putchar('\n');
}

void
run_test(void)
{
    quicksort(0, NELEMS-1);
}

int
main(void)
{
    run_test();
    for (unsigned int i = 0; i < NELEMS; i++)
        write_hex_number_to_stdout(arr[i]);
    
    return 0;
}
