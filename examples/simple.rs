#![feature(proc_macro_hygiene)]

fn main() {
    let mut offset = 0;
    let bytes = &[
        0xf6, 0x64, // mov a, 100
        0xf3, 0xFF, // mov b, -1
        0x0b        // add a, b
    ];
    println!("{:?}", decode(bytes, &mut offset));
    println!("{:?}", decode(bytes, &mut offset));
    println!("{:?}", decode(bytes, &mut offset));
}

#[derive(Debug)]
enum Reg {
    Pc,
    Sp,
    A,
    B,
}

#[derive(Debug)]
enum Instruction {
    Load(Reg, Reg, u32),
    Store(Reg, Reg, u32),
    Op(Op, Reg, Reg),
    OpImm(Op, Reg, u32),
    Branch(u8),
    Invalid,
}

#[derive(Debug)]
enum Op {
    Mov,
    Add,
    Sub,
    Or,
    Xor,
    And,
    Lsh,
    Rsh,
}

fn decode(bytes: &[u8], offset: &mut usize) -> Instruction {
    // A closure that reads a single byte from the `bytes` array and increments the offset
    let mut read_u8 = || {
        *offset += 1;
        bytes[*offset - 1]
    };

    bit_match::match_bits! {
        // Specify to the bit-match macro that 8 bits can be read by calling the `read_u8` function
        read 8 => read_u8();

        0000 ss dd => Instruction::Op(Op::Add, reg(d), reg(s)),
        0001 ss dd => Instruction::Op(Op::Sub, reg(d), reg(s)),
        0010 ss dd => Instruction::Op(Op::Or,  reg(d), reg(s)),
        0011 ss dd => Instruction::Op(Op::Xor, reg(d), reg(s)),
        0100 ss dd => Instruction::Op(Op::And, reg(d), reg(s)),

        0101 nn dd => Instruction::OpImm(Op::Rsh, reg(d), n as u32 + 1),
        0110 nn dd => Instruction::OpImm(Op::Lsh, reg(d), n as u32 + 1),
        0111 nn dd => Instruction::Invalid,

        1000 ss dd iiiiiiii => Instruction::Load(reg(d), reg(s), i as u32),
        1001 ss dd iiiiiiii => Instruction::Store(reg(d), reg(s), i as u32),

        1010 cc cc => Instruction::Branch(c),
        1011 xx xx => Instruction::Invalid,
        1100 xx xx => Instruction::Invalid,
        1101 xx xx => Instruction::Invalid,
        1110 xx xx => Instruction::Invalid,

        1111 00 dd iiiiiiii          => Instruction::OpImm(Op::Mov, reg(d), sxt_8(i)),
        1111 01 dd iiiiiiii          => Instruction::OpImm(Op::Mov, reg(d), zxt_8(i)),
        1111 10 dd iiiiiiii iiiiiiii => Instruction::OpImm(Op::Mov, reg(d), sxt_16(i)),
        1111 11 dd iiiiiiii iiiiiiii => Instruction::OpImm(Op::Mov, reg(d), zxt_16(i)),
    }
}

fn reg(reg: u8) -> Reg {
    match reg {
        0 => Reg::Pc,
        1 => Reg::Sp,
        2 => Reg::A,
        3 => Reg::B,
        _ => panic!("Bad register"),
    }
}

fn sxt_8(value: u8) -> u32 {
    value as i8 as i32 as u32
}
fn zxt_8(value: u8) -> u32 {
    value as u32
}
fn sxt_16(value: u16) -> u32 {
    value as i16 as i32 as u32
}
fn zxt_16(value: u16) -> u32 {
    value as u32
}