#include <assert.h>
int main(void) {
    unsigned char data[2] = {3, 4};
    unsigned char *alias = &data[1];
    *alias = 7;
    assert(data[0] == 3 && data[1] == 7);
    return 0;
}
