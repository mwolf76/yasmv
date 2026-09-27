int side = 0;
int conditional(void)
{
    int x = 3;
    if (x > 5) side = 99;
    else side = 2;
    x = x + side;
    return x;
}
int nested(void)
{
    int sum = 0;
    for (int i = 0; i < 3; ++i)
        for (int j = 0; j < 4; ++j)
            sum += i * 4 + j;
    return sum;
}
void endless(void)
{
    for (;;) side = side ^ 1;
}
