#include "add.h"

uint64_t fib(uint64_t x) {
    if (x < 2) {
	return x;
    } else {
	return add_xyx(fib(x-1), fib(x - 2));
    }
}
