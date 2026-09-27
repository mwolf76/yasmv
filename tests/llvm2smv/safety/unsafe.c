#include <assert.h>
#include <yasmv.h>
static int increment(int value) {
    return value + 1;
}
int main(void) {
    int value = __VERIFIER_nondet_int();
    __VERIFIER_assume(value >= 0 && value <= 2);
    assert(increment(value) <= 2);
    return 0;
}
