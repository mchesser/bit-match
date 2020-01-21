# bit-match

A procedural macro for matching fixed bits and extracting variable bits from a bit-stream.

### Example

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
        1011 xxxx => format!("invalid"),
        1100 xxxx => format!("invalid"),
        1101 xxxx => format!("invalid"),
        1110 xxxx => format!("invalid"),

        // Fixed bits can be named constants
        const LOAD_IMM = 1111;

        // Global symbols are allowed in pattern substitution
        pattern loadi(opcode, imm) => (LOAD_IMM opcode dst imm);
        loadi(00, imm8) => format!("li r{}, #{}", dst, imm8),
        loadi(01, imm8) => format!("li r{}, #{}", dst, imm8),
        loadi(10, imm16) => format!("li r{}, #{}", dst, imm16),
        loadi(11, imm16) => format!("li r{}, #{}", dst, imm16),
    }
}
```