#![feature(proc_macro_hygiene)]

fn main() {
    let mut offset = 0;
    let bytes = &[
        0xf6, 0x64, // mov a, 100
        0xf3, 0xFF, // mov b, -1
        0x0b, // add a, b
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
    let mut read_u8 = || {
        *offset += 1;
        bytes[*offset - 1]
    };

    bit_match::match_bits! {
        read 8 => read_u8();

        var src: 2;
        var dst: 2;
        var imm8: 8;
        var imm16: 16;
        var cond: 4;
        var shift: 2;

        pattern op(opcode) => (opcode src dst);
        op(0000) => Instruction::Op(Op::Add, reg(dst), reg(src)),
        op(0001) => Instruction::Op(Op::Sub, reg(dst), reg(src)),
        op(0010) => Instruction::Op(Op::Or,  reg(dst), reg(src)),
        op(0011) => Instruction::Op(Op::Xor, reg(dst), reg(src)),
        op(0100) => Instruction::Op(Op::And, reg(dst), reg(src)),

        pattern shift(opcode) => (opcode shift dst);
        shift(0101) => Instruction::OpImm(Op::Rsh, reg(dst), shift as u32 + 1),
        shift(0110) => Instruction::OpImm(Op::Lsh, reg(dst), shift as u32 + 1),
        shift(0111) => Instruction::Invalid,

        pattern mem(opcode) => (opcode src dst imm8);
        mem(1000) => Instruction::Load(reg(dst), reg(src), imm8 as u32),
        mem(1001) => Instruction::Store(reg(dst), reg(src), imm8 as u32),

        1010 cond => Instruction::Branch(cond),
        1011 xxxx => Instruction::Invalid,
        1100 xxxx => Instruction::Invalid,
        1101 xxxx => Instruction::Invalid,
        1110 xxxx => Instruction::Invalid,

        pattern loadi(opcode, imm) => (1111 opcode dst imm);
        loadi(00, imm8)  => Instruction::OpImm(Op::Mov, reg(dst), sxt_8(imm8)),
        loadi(01, imm8)  => Instruction::OpImm(Op::Mov, reg(dst), zxt_8(imm8)),
        loadi(10, imm16) => Instruction::OpImm(Op::Mov, reg(dst), sxt_16(imm16)),
        loadi(11, imm16) => Instruction::OpImm(Op::Mov, reg(dst), zxt_16(imm16)),
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
