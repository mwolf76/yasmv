// Simple counter example for testing LLVM to SMV translation

int counter = 0;
const int limit = 10;

int main()
{
    while (counter < limit) {
        counter = counter + 1;
    }
    return 0;
}
