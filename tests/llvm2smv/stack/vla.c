#include <yasmv.h>
#include <assert.h>

int main(void)
{
    unsigned char n = __VERIFIER_nondet_bool() ? 1 : 2;
    unsigned char a[n];
    a[0] = 7;
    assert(a[0] == 7);
    return 0;
}
