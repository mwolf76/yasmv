// Example with conditional logic

int x = 0;
int y = 0;

int main()
{
    if (x > 5) {
        y = 1;
    } else {
        y = 2;
    }

    x = x + 1;

    if (x == 10) {
        y = 0;
    }

    return y;
}
