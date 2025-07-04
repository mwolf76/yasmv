# LLVM to SMV Translator

This tool translates C programs (via LLVM IR) to SMV models for formal verification with yasmv.

## Building

### Prerequisites

- LLVM development libraries (version 10+ recommended)
- Make
- C++20 compiler (g++ 10+ or clang++ 10+)

On Ubuntu/Debian:
```bash
sudo apt-get install llvm-dev clang build-essential
```

On other systems, install the LLVM development packages for your distribution.

### Compilation

```bash
make
```

Check dependencies:
```bash
make deps
```

## Usage

### Step 1: Compile C to LLVM IR

```bash
clang -S -emit-llvm -O0 program.c -o program.ll
```

Or use the provided script:
```bash
cd examples/simple
./compile.sh counter.c
```

### Step 2: Translate LLVM IR to SMV

```bash
./llvm2smv program.ll -o program.smv
```

Options:
- `-o <file>` : Output SMV file (default: stdout)
- `--word-width <n>` : Default integer width (default: 32)
- `-v` : Verbose output

## Examples

### Simple Counter
```c
int counter = 0;
const int limit = 10;

int main() {
    while (counter < limit) {
        counter = counter + 1;
    }
    return 0;
}
```

Translates to SMV model with:
- Variables for counter and limit
- Program counter tracking control flow
- Transitions modeling the loop

### Running with yasmv

```bash
# Compile and translate
clang -S -emit-llvm -O0 counter.c -o counter.ll
./llvm2smv counter.ll -o counter.smv

# Verify with yasmv
yasmv counter.smv
>> reach counter = 10
```

## Current Limitations

1. **Bounded loops only** - All loops must terminate
2. **No dynamic memory** - malloc/free not supported
3. **No function pointers** - Direct calls only
4. **Limited pointer support** - Pointers abstracted as integers
5. **No floating point** - Integer arithmetic only
6. **No I/O operations** - Pure computation only

## Architecture

The translator works in phases:

1. **Type Translation**: LLVM types → SMV types
2. **Variable Extraction**: Function arguments, locals → SMV variables
3. **Control Flow**: Basic blocks → Program counter states
4. **Expression Translation**: LLVM instructions → SMV expressions
5. **SMV Generation**: Output well-formed SMV model

## Extending

To add support for new LLVM instructions:

1. Add handler in `ExprTranslator::translateInstruction()`
2. Implement translation logic
3. Add test case

To support new C features:

1. Identify LLVM IR pattern
2. Design SMV representation
3. Implement translation

## Troubleshooting

- **"Unknown instruction"**: Not all LLVM instructions are supported yet
- **"Struct types not supported"**: Flatten structs or use separate variables
- **Large state space**: Use smaller data types or abstract the problem

## Future Work

- [ ] Memory modeling with arrays
- [ ] Function call support via modules
- [ ] Automatic property generation
- [ ] Pointer analysis
- [ ] Loop bound inference
- [ ] Floating point abstraction
