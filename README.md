# bit-match

A procedural macro for matching fixed bits and extracting variable bits from a bit-stream.

## Example

```rust
/// Disassembles the instruction at `offset` in `bytes`
fn disasm(bytes: &[u8], offset: &mut usize) -> String {
    // A closure that reads a single byte from the `bytes` array and increments the offset
    let mut read_u8 = || {
        *offset += 1;
        bytes[*offset - 1]
    };

    bit_match::match_bits! {
        // Specify to the bit-match macro that 8 bits can be read by calling the `read_u8` function
        read 8 => read_u8();

        // Define variables to store variable bits of a fixed length
        var src: 2;
        var dst: 2;
        var imm8: 8;
        var imm16: 16;
        var shift: 2;

        // Define a pattern for a group of instructions
        pattern op(opcode) => (opcode src dst);
        op(0000) => format!("add r{}, r{}", dst, src),
        op(0001) => format!("sub r{}, r{}", dst, src),
        op(0010) => format!("or r{}, r{}",  dst, src),
        op(0011) => format!("xor r{}, r{}", dst, src),
        op(0100) => format!("and r{}, r{}", dst, src),

        pattern shift(opcode) => (opcode shift dst);
        shift(0101) => format!("rsh r{}, {}", dst, shift + 1),
        shift(0110) => format!("lsh r{}, {}", dst, shift + 1),
        shift(0111) => format!("invalid"),

        // Bits are read on demand allowing for variable length decoding
        pattern mem(opcode) => (opcode src dst imm8);
        mem(1000) => format!("load {}, [r{} + {}]", dst, src, imm8),
        mem(1001) => format!("store {}, [r{} + {}]", dst, src, imm8 as u32),

        // For simple or unique instructions it is not necessary to define variables, or patterns
        // an inline variable is automatically created for each group of variable bits with the same
        // character, with length defined based on the number of times the character is repeated
        1010 aaaa => format!("jz {}", a),

        // Fixed bits can be named constants
        const LOAD_IMM = 1111;

        // Global symbols are allowed in pattern substitution
        pattern loadi(opcode, imm) => (LOAD_IMM opcode dst imm);
        loadi(00, imm8) => format!("li r{}, #{}", dst, imm8),
        loadi(01, imm8) => format!("lu r{}, #{}", dst, imm8),
        loadi(10, imm16) => format!("li r{}, #{}", dst, imm16),
        loadi(11, imm16) => format!("lu r{}, #{}", dst, imm16),

        // The `_` character can be used to define a default case for bits
        ____ ____ => format!("invalid"),
    }
```

## Features

### Overlap checking

Bit-match checks for cases where bits overlap any where within the tree, e.g.:

```
error: 2 matches overlap when mask is 000000
error: Match is 111111xxxxxxxxxxxxxxxxxx here:
   |
65 |         loadi(11, imm16) => format!("li r{}, #{}", dst, imm16),
   |         ^^^^^
error: Match is 11111100 here:
   |
67 |         1111 1100 => format!("overlapping"),
   |         ^^^^^^^^^
```

### Exhaustiveness checking

Bit-match checks for cases where there are bits still left to match, and there are no default case

```
error: Not all cases covered for: ???????__________001_____0010011
error: Not all cases covered for: ???????__________101_____0010011
```
