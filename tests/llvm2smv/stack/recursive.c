#include <assert.h>

static _Bool flip(_Bool n)
{
    if (n)
        return !flip(0);
    return 0;
}

int main(void)
{
    assert(flip(1) == 1);
    return 0;
}
