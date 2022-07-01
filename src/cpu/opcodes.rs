#[derive(Debug, Copy, Clone)]
pub struct OpCode {
    pub instruction: Instruction,
    pub addressing_mode: AddressingMode,
}

impl From<u8> for OpCode {
    fn from(opcode: u8) -> Self {
        use AddressingMode::*;
        use BranchInstruction::*;
        use ImpliedInstruction::*;
        use Instruction::*;
        use PullInstruction::*;
        use PushInstruction::*;
        use ReadInstruction::*;
        use ReadWriteInstruction::*;
        use WriteInstruction::*;
        let (instruction, addressing_mode) = match opcode {
            0x00 => (Brk, AddressingMode::Implied),
            0x01 => (Read(Ora), IndirectX),
            0x05 => (Read(Ora), ZeroPage),
            0x06 => (ReadWrite(Asl), ZeroPage),
            0x08 => (Push(Php), AddressingMode::Implied),
            0x09 => (Read(Ora), Immediate),
            0x0a => (ReadWrite(Asl), Accumulator),
            0x0d => (Read(Ora), Absolute),
            0x0e => (ReadWrite(Asl), Absolute),
            0x10 => (Branch(Bpl), Relative),
            0x11 => (Read(Ora), IndirectY),
            0x15 => (Read(Ora), ZeroPageX),
            0x16 => (ReadWrite(Asl), ZeroPageX),
            0x18 => (Instruction::Implied(Clc), AddressingMode::Implied),
            0x19 => (Read(Ora), AbsoluteY),
            0x1d => (Read(Ora), AbsoluteX),
            0x1e => (ReadWrite(Asl), AbsoluteX),
            0x20 => (Jsr, Absolute),
            0x21 => (Read(And), IndirectX),
            0x24 => (Read(Bit), ZeroPage),
            0x25 => (Read(And), ZeroPage),
            0x26 => (ReadWrite(Rol), ZeroPage),
            0x28 => (Pull(Plp), AddressingMode::Implied),
            0x29 => (Read(And), Immediate),
            0x2a => (ReadWrite(Rol), Accumulator),
            0x2c => (Read(Bit), Absolute),
            0x2d => (Read(And), Absolute),
            0x2e => (ReadWrite(Rol), Absolute),
            0x30 => (Branch(Bmi), Relative),
            0x31 => (Read(And), IndirectY),
            0x35 => (Read(And), ZeroPageX),
            0x36 => (ReadWrite(Rol), ZeroPageX),
            0x38 => (Instruction::Implied(Sec), AddressingMode::Implied),
            0x39 => (Read(And), AbsoluteY),
            0x3d => (Read(And), AbsoluteX),
            0x3e => (ReadWrite(Rol), AbsoluteX),
            0x40 => (Rti, AddressingMode::Implied),
            0x41 => (Read(Eor), IndirectX),
            0x45 => (Read(Eor), ZeroPage),
            0x46 => (ReadWrite(Lsr), ZeroPage),
            0x48 => (Push(Pha), AddressingMode::Implied),
            0x49 => (Read(Eor), Immediate),
            0x4a => (ReadWrite(Lsr), Accumulator),
            0x4c => (Jmp, Absolute),
            0x4d => (Read(Eor), Absolute),
            0x4e => (ReadWrite(Lsr), Absolute),
            0x50 => (Branch(Bvc), Relative),
            0x51 => (Read(Eor), IndirectY),
            0x55 => (Read(Eor), ZeroPageX),
            0x56 => (ReadWrite(Lsr), ZeroPageX),
            0x58 => (Instruction::Implied(Cli), AddressingMode::Implied),
            0x59 => (Read(Eor), AbsoluteY),
            0x5d => (Read(Eor), AbsoluteX),
            0x5e => (ReadWrite(Lsr), AbsoluteX),
            0x60 => (Rts, AddressingMode::Implied),
            0x61 => (Read(Adc), IndirectX),
            0x65 => (Read(Adc), ZeroPage),
            0x66 => (ReadWrite(Ror), ZeroPage),
            0x68 => (Pull(Pla), AddressingMode::Implied),
            0x69 => (Read(Adc), Immediate),
            0x6a => (ReadWrite(Ror), Accumulator),
            0x6c => (JmpIndirect, Absolute),
            0x6d => (Read(Adc), Absolute),
            0x6e => (ReadWrite(Ror), AbsoluteX),
            0x70 => (Branch(Bvs), Relative),
            0x71 => (Read(Adc), IndirectY),
            0x75 => (Read(Adc), ZeroPageX),
            0x76 => (ReadWrite(Ror), ZeroPageX),
            0x78 => (Instruction::Implied(Sei), AddressingMode::Implied),
            0x79 => (Read(Adc), AbsoluteY),
            0x7d => (Read(Adc), AbsoluteX),
            0x7e => (ReadWrite(Ror), Absolute),
            0x81 => (Write(Sta), IndirectX),
            0x84 => (Write(Sty), ZeroPage),
            0x85 => (Write(Sta), ZeroPage),
            0x86 => (Write(Stx), ZeroPage),
            0x88 => (Instruction::Implied(Dey), AddressingMode::Implied),
            0x8a => (Instruction::Implied(Txa), AddressingMode::Implied),
            0x8c => (Write(Sty), Absolute),
            0x8d => (Write(Sta), Absolute),
            0x8e => (Write(Stx), Absolute),
            0x90 => (Branch(Bcc), Relative),
            0x91 => (Write(Sta), IndirectY),
            0x94 => (Write(Sty), ZeroPageX),
            0x95 => (Write(Sta), ZeroPageX),
            0x96 => (Write(Stx), ZeroPageY),
            0x98 => (Instruction::Implied(Tya), AddressingMode::Implied),
            0x99 => (Write(Sta), AbsoluteY),
            0x9a => (Instruction::Implied(Txs), AddressingMode::Implied),
            0x9d => (Write(Sta), AbsoluteX),
            0xa0 => (Read(Ldy), Immediate),
            0xa1 => (Read(Lda), IndirectX),
            0xa2 => (Read(Ldx), Immediate),
            0xa4 => (Read(Ldy), ZeroPage),
            0xa5 => (Read(Lda), ZeroPage),
            0xa6 => (Read(Ldx), ZeroPage),
            0xa8 => (Instruction::Implied(Tay), AddressingMode::Implied),
            0xa9 => (Read(Lda), Immediate),
            0xaa => (Instruction::Implied(Tax), AddressingMode::Implied),
            0xac => (Read(Ldy), Absolute),
            0xad => (Read(Lda), Absolute),
            0xae => (Read(Ldx), Absolute),
            0xb0 => (Branch(Bcs), Relative),
            0xb1 => (Read(Lda), IndirectY),
            0xb4 => (Read(Ldy), ZeroPageX),
            0xb5 => (Read(Lda), ZeroPageX),
            0xb6 => (Read(Ldx), ZeroPageY),
            0xb8 => (Instruction::Implied(Clv), AddressingMode::Implied),
            0xb9 => (Read(Lda), AbsoluteY),
            0xba => (Instruction::Implied(Tsx), AddressingMode::Implied),
            0xbc => (Read(Ldy), AbsoluteX),
            0xbd => (Read(Lda), AbsoluteX),
            0xbe => (Read(Ldx), AbsoluteY),
            0xc0 => (Read(Cpy), Immediate),
            0xc1 => (Read(Cmp), IndirectX),
            0xc4 => (Read(Cpy), ZeroPage),
            0xc5 => (Read(Cmp), ZeroPage),
            0xc6 => (ReadWrite(Dec), ZeroPage),
            0xc8 => (Instruction::Implied(Iny), AddressingMode::Implied),
            0xc9 => (Read(Cmp), Immediate),
            0xca => (Instruction::Implied(Dex), AddressingMode::Implied),
            0xcc => (Read(Cpy), Absolute),
            0xcd => (Read(Cmp), Absolute),
            0xce => (ReadWrite(Dec), Absolute),
            0xd0 => (Branch(Bne), Relative),
            0xd1 => (Read(Cmp), IndirectY),
            0xd5 => (Read(Cmp), ZeroPageX),
            0xd6 => (ReadWrite(Dec), ZeroPageX),
            0xd8 => (Instruction::Implied(Cld), AddressingMode::Implied),
            0xd9 => (Read(Cmp), AbsoluteY),
            0xdd => (Read(Cmp), AbsoluteX),
            0xde => (ReadWrite(Dec), AbsoluteX),
            0xe0 => (Read(Cpx), Immediate),
            0xe1 => (Read(Sbc), IndirectX),
            0xe4 => (Read(Cpx), ZeroPage),
            0xe5 => (Read(Sbc), ZeroPage),
            0xe6 => (ReadWrite(Inc), ZeroPage),
            0xe8 => (Instruction::Implied(Inx), AddressingMode::Implied),
            0xe9 => (Read(Sbc), Immediate),
            0xea => (Instruction::Implied(Nop), AddressingMode::Implied),
            0xec => (Read(Cpx), Absolute),
            0xed => (Read(Sbc), Absolute),
            0xee => (ReadWrite(Inc), Absolute),
            0xf0 => (Branch(Beq), Relative),
            0xf1 => (Read(Sbc), IndirectY),
            0xf5 => (Read(Sbc), ZeroPageX),
            0xf6 => (ReadWrite(Inc), ZeroPageX),
            0xf8 => (Instruction::Implied(Sed), AddressingMode::Implied),
            0xf9 => (Read(Sbc), AbsoluteY),
            0xfd => (Read(Sbc), AbsoluteX),
            0xfe => (ReadWrite(Inc), AbsoluteX),
            _ => unimplemented!("opcode 0x{:02x} not implemented", opcode),
        };
        OpCode {
            instruction,
            addressing_mode,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Instruction {
    Read(ReadInstruction),
    Write(WriteInstruction),
    ReadWrite(ReadWriteInstruction),
    Branch(BranchInstruction),
    Implied(ImpliedInstruction),
    Push(PushInstruction),
    Pull(PullInstruction),
    Brk,
    Rti,
    Rts,
    Jmp,
    JmpIndirect,
    Jsr,
}

#[derive(Debug, Copy, Clone)]
pub enum ReadInstruction {
    Lda,
    Ldx,
    Ldy,
    Eor,
    And,
    Ora,
    Adc,
    Sbc,
    Cmp,
    Bit,
    Cpx,
    Cpy,
}

#[derive(Debug, Copy, Clone)]
pub enum WriteInstruction {
    Sta,
    Stx,
    Sty,
}

#[derive(Debug, Copy, Clone)]
pub enum ReadWriteInstruction {
    Inc,
    Dec,
    Asl,
    Rol,
    Lsr,
    Ror,
}

#[derive(Debug, Copy, Clone)]
pub enum BranchInstruction {
    Bcc,
    Bcs,
    Beq,
    Bmi,
    Bne,
    Bpl,
    Bvc,
    Bvs,
}

#[derive(Debug, Copy, Clone)]
pub enum ImpliedInstruction {
    Clc,
    Cld,
    Cli,
    Clv,
    Dex,
    Dey,
    Inx,
    Iny,
    Nop,
    Sec,
    Sed,
    Sei,
    Tax,
    Tay,
    Tsx,
    Txa,
    Txs,
    Tya,
}

#[derive(Debug, Copy, Clone)]
pub enum PushInstruction {
    Pha,
    Php,
}

#[derive(Debug, Copy, Clone)]
pub enum PullInstruction {
    Pla,
    Plp,
}

#[derive(Debug, Copy, Clone)]
pub enum AddressingMode {
    IndirectX,
    ZeroPage,
    Immediate,
    Absolute,
    IndirectY,
    ZeroPageX,
    ZeroPageY,
    AbsoluteY,
    AbsoluteX,
    Accumulator,
    Implied,
    Relative,
}
