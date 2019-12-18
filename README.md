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

        // Fixed bits are specified with '0's and '1's, variable bits are specified as characters,
        // and are concatenated together
        0000 ss dd => format!("add r{}, r{}", d, s),
        0001 ss dd => format!("sub r{}, r{}", d, s),
        0010 ss dd => format!("or  r{}, r{}",  d, s),
        0011 ss dd => format!("xor r{}, r{}", d, s),
        0100 ss dd => format!("and r{}, r{}", d, s),
        0101 nn dd => format!("rsh r{}, {}", d, n + 1),
        0110 nn dd => format!("lsh r{}, {}", d, n + 1),
        0111 nn dd => format!("invalid"),

        // Bits are read on demand allowing for variable length decoding
        1000 ss dd iiiiiiii => format!("load {}, [r{} + {}]", d, s, i),
        1001 ss dd iiiiiiii => format!("store {}, [r{} + {}]", d, s, i as u32),

        1010 cc cc => format!("jz {}", c),
        1011 xx xx => format!("invalid"),
        1100 xx xx => format!("invalid"),
        1101 xx xx => format!("invalid"),
        1110 xx xx => format!("invalid"),

        1111 00 dd iiiiiiii          => format!("lu r{}, #{}", d, i),
        1111 01 dd iiiiiiii          => format!("li r{}, #{}", d, i),
        1111 10 dd iiiiiiii iiiiiiii => format!("lu r{}, #{}", d, i),
        1111 11 dd iiiiiiii iiiiiiii => format!("li r{}, #{}", d, i),
    }
}
```