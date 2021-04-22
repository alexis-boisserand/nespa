#[cfg(test)]
mod tests;

use bitflags::bitflags;
use num_traits::FromPrimitive;

macro_rules! set_reg {
    ($self:ident, $field:ident, $value:expr) => {
        $self.set_zero_and_negative_flags($value);
        $self.$field = $value;
    };
}

const P_INIT_VALUE: u8 = 0x34;
const S_INIT_VALUE: u8 = 0xFD;
const RESET_VECTOR: u16 = 0xFFFC;

bitflags! {
    struct Flags: u8 {
        const C = 0x1;
        const Z = 0x2;
        const I = 0x4;
        const D = 0x10;
        const B = 0x20;
        const V = 0x40;
        const N = 0x80;
    }
}

#[derive(Debug, Copy, Clone)]
struct OpCode {
    instruction: Instruction,
    instruction_kind: InstructionKind,
    addressing_mode: AddressingMode,
}

impl OpCode {
    fn new(opcode: u8) -> Self {
        let instruction = Instruction::from(opcode);
        let instruction_kind = InstructionKind::from(instruction);
        let addressing_mode = AddressingMode::from(opcode);
        Self {
            instruction,
            instruction_kind,
            addressing_mode,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, num_derive::FromPrimitive)]
enum Instruction {
    Ora = 0b01000,
    And,
    Eor,
    Adc,
    Sta,
    Lda,
    Cmp,
    Sbc,
    Asl = 0b10000,
    Rol,
    Lsr,
    Ror,
    Stx,
    Ldx,
    Dec,
    Inc,
    Bit = 0b00001,
    Jmp,
    JmpAbs,
    Sty,
    Ldy,
    Cpy,
    Cpx,
}

impl From<u8> for Instruction {
    fn from(opcode: u8) -> Self {
        // instructions are of the form aaabbbcc
        // where the combination of aaa and cc determine the opcode
        // and bbb the addressing mode
        let aaa = opcode >> 5;
        let cc = opcode & 0x3;
        let instruction = (cc << 3) | aaa;
        Instruction::from_u8(instruction).expect("invalid instruction")
    }
}

#[derive(Debug, Copy, Clone)]
enum InstructionKind {
    Read,
    ReadWrite,
    Write,
}

impl From<Instruction> for InstructionKind {
    fn from(instruction: Instruction) -> Self {
        match instruction {
            Instruction::Lda
            | Instruction::Ldx
            | Instruction::Ldy
            | Instruction::Eor
            | Instruction::And
            | Instruction::Ora
            | Instruction::Adc
            | Instruction::Sbc
            | Instruction::Cmp
            | Instruction::Bit => InstructionKind::Read,
            Instruction::Sta | Instruction::Stx | Instruction::Sty => InstructionKind::Write,
            Instruction::Inc
            | Instruction::Dec
            | Instruction::Asl
            | Instruction::Rol
            | Instruction::Lsr
            | Instruction::Ror => InstructionKind::ReadWrite,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum AddressingMode {
    IndirectX,
    Zeropage,
    Immediate,
    Absolute,
    IndirectY,
    ZeroPageX,
    AbsoluteY,
    AbsoluteX,
    Accumulator,
    Implied,
}

impl From<u8> for AddressingMode {
    fn from(opcode: u8) -> Self {
        let cc = opcode & 0x3;
        let bbb = (opcode >> 2) & 0x7;

        match cc {
            0x00 => match bbb {
                0x00 => AddressingMode::Immediate,
                0x01 => AddressingMode::Zeropage,
                0x03 => AddressingMode::Absolute,
                0x05 => AddressingMode::ZeroPageX,
                0x07 => AddressingMode::AbsoluteX,
                _ => panic!("invalid addressing mode, opcode: {:?}", opcode),
            },
            0x01 => match bbb {
                0x00 => AddressingMode::IndirectX,
                0x01 => AddressingMode::Zeropage,
                0x02 => AddressingMode::Immediate,
                0x03 => AddressingMode::Absolute,
                0x04 => AddressingMode::IndirectY,
                0x05 => AddressingMode::ZeroPageX,
                0x06 => AddressingMode::AbsoluteY,
                0x07 => AddressingMode::AbsoluteX,
                _ => panic!("invalid addressing mode, opcode: {:?}", opcode),
            },
            0x02 => match bbb {
                0x00 => AddressingMode::Immediate,
                0x01 => AddressingMode::Zeropage,
                0x02 => AddressingMode::Accumulator,
                0x03 => AddressingMode::Absolute,
                0x05 => AddressingMode::ZeroPageX,
                0x07 => AddressingMode::AbsoluteX,
                _ => panic!("invalid addressing mode, opcode: {:?}", opcode),
            },
            _ => panic!("invalid addressing mode, opcode: {:?}", opcode),
        }
    }
}

#[derive(Debug)]
enum CpuState {
    FetchOpCode,
    FetchValue0,
    FetchValue1(Option<u8>),
    Accumulator,
    ReadOrWrite,
    ZeroPageX,
    PageCrossing,
    IndirectX0,
    IndirectX1,
    IndirectX2,
    IndirectY0,
    IndirectY1,
    ReadInstruction,
    ReadWriteInstruction(u16),
    WriteBack(u16),
}

#[derive(Debug)]
pub struct Cpu {
    a: u8,
    x: u8,
    y: u8,
    pc: u16,
    s: u8,
    p: Flags,
    mem: [u8; 0xFFFF],
    state: CpuState,
    opcode: OpCode,
    value0: u8,
    value1: u8,
}

impl Cpu {
    pub fn new() -> Self {
        Self {
            a: 0,
            x: 0,
            y: 0,
            pc: 0, // pc must be read at addresses 0xFFFC and 0xFFFD
            s: S_INIT_VALUE,
            p: Flags::from_bits(P_INIT_VALUE).unwrap(),
            mem: [0; 0xFFFF],
            state: CpuState::FetchOpCode,
            // actual initial values don't matter the next 3 fields
            opcode: OpCode::new(0x69),
            value0: 0,
            value1: 0,
        }
    }

    pub fn tick(&mut self) {
        self.state = match self.state {
            CpuState::FetchOpCode => self.fetch_opcode(),
            CpuState::FetchValue0 => {
                self.value0 = self.read_mem(self.pc);
                self.value1 = 0;
                self.increment_pc(); // in the case of single byte instruction, the following byte is read and discarded
                match self.opcode.addressing_mode {
                    AddressingMode::Accumulator => CpuState::Accumulator,
                    AddressingMode::IndirectX => CpuState::IndirectX0,
                    AddressingMode::Zeropage => CpuState::ReadOrWrite,
                    AddressingMode::Immediate => CpuState::ReadInstruction,
                    AddressingMode::Absolute => CpuState::FetchValue1(None),
                    AddressingMode::IndirectY => CpuState::IndirectY0,
                    AddressingMode::ZeroPageX => CpuState::ZeroPageX,
                    AddressingMode::AbsoluteY => CpuState::FetchValue1(Some(self.y)),
                    AddressingMode::AbsoluteX => CpuState::FetchValue1(Some(self.x)),
                    _ => unimplemented!("unknown addressing mode"),
                }
            }
            CpuState::FetchValue1(index) => {
                self.value1 = self.read_mem(self.pc);
                self.increment_pc();
                match index {
                    Some(register) => {
                        let (value, pagebound_crossed) = self.value0.overflowing_add(register);
                        self.value0 = value;
                        if pagebound_crossed {
                            CpuState::PageCrossing
                        } else {
                            CpuState::ReadOrWrite
                        }
                    }
                    None => CpuState::ReadOrWrite,
                }
            }
            CpuState::Accumulator => {
                self.a = self.execute_read_write_instruction(self.a);
                self.fetch_opcode()
            }
            CpuState::ReadOrWrite => {
                let address = (self.value1 as u16) << 8 | self.value0 as u16;
                match self.opcode.instruction_kind {
                    InstructionKind::Read => {
                        self.value0 = self.read_mem(address);
                        CpuState::ReadInstruction
                    }
                    InstructionKind::ReadWrite => {
                        self.value0 = self.read_mem(address);
                        CpuState::ReadWriteInstruction(address)
                    }
                    InstructionKind::Write => {
                        let value = match self.opcode.instruction {
                            Instruction::Sta => self.a,
                            Instruction::Stx => self.x,
                            Instruction::Sty => self.y,
                            _ => unreachable!(),
                        };
                        self.write_mem(address, value);
                        CpuState::FetchOpCode
                    }
                    _ => unimplemented!(),
                }
            }
            CpuState::ZeroPageX => {
                self.value0 = self.value0.wrapping_add(self.x);
                CpuState::ReadOrWrite
            }
            CpuState::PageCrossing => {
                self.value1 = self.value1.wrapping_add(1);
                CpuState::ReadOrWrite
            }
            CpuState::IndirectX0 => {
                self.value0 = self.value0.wrapping_add(self.x);
                CpuState::IndirectX1
            }
            CpuState::IndirectX1 => {
                self.value1 = self.value0.wrapping_add(1);
                self.value0 = self.read_mem(self.value0 as u16);
                CpuState::IndirectX2
            }
            CpuState::IndirectX2 => {
                self.value1 = self.read_mem(self.value1 as u16);
                CpuState::ReadOrWrite
            }
            CpuState::IndirectY0 => {
                self.value1 = self.value0.wrapping_add(1);
                self.value0 = self.read_mem(self.value0 as u16);
                CpuState::IndirectY1
            }
            CpuState::IndirectY1 => {
                self.value1 = self.read_mem(self.value1 as u16);
                let (value, pagebound_crossed) = self.value0.overflowing_add(self.y);
                self.value0 = value;
                if pagebound_crossed {
                    CpuState::PageCrossing
                } else {
                    CpuState::ReadOrWrite
                }
            }
            CpuState::ReadInstruction => {
                match self.opcode.instruction {
                    Instruction::Adc => self.adc(),
                    Instruction::And => self.and(),
                    Instruction::Bit => self.bit(),
                    Instruction::Cmp => self.cmp(),
                    Instruction::Eor => self.eor(),
                    Instruction::Lda => self.lda(),
                    Instruction::Ldx => self.ldx(),
                    Instruction::Ldy => self.ldy(),
                    Instruction::Ora => self.ora(),
                    Instruction::Sbc => self.sbc(),
                    _ => todo!(),
                };
                self.fetch_opcode()
            }
            CpuState::ReadWriteInstruction(address) => {
                // in theory, at this point, self.value0 is written to address
                // right before executing the instruction
                self.value0 = self.execute_read_write_instruction(self.value0);
                CpuState::WriteBack(address)
            }
            CpuState::WriteBack(address) => {
                self.write_mem(address, self.value0);
                CpuState::FetchOpCode
            }
        };
    }

    pub fn reset(&mut self) {
        // TODO initialize other registers
        self.pc = self.read_mem_u16(RESET_VECTOR);
        self.state = CpuState::FetchOpCode;
    }

    fn read_mem(&self, address: u16) -> u8 {
        self.mem[address as usize]
    }

    // FIXME: Can potentially panic, check address value.
    fn read_mem_u16(&self, address: u16) -> u16 {
        let mut value = [0u8; 2];
        let address = address as usize;
        value.copy_from_slice(&self.mem[address..address + 2]);
        u16::from_le_bytes(value)
    }

    fn write_mem(&mut self, address: u16, value: u8) {
        self.mem[address as usize] = value;
    }

    fn write_mem_u16(&mut self, address: u16, value: u16) {
        let value = value.to_le_bytes();
        let address = address as usize;
        &self.mem[address..address + 2]
            .iter_mut()
            .zip(value.iter())
            .for_each(|(dest, src)| *dest = *src);
    }

    fn fetch_opcode(&mut self) -> CpuState {
        self.opcode = OpCode::new(self.read_mem(self.pc));
        self.increment_pc();
        CpuState::FetchValue0
    }

    fn increment_pc(&mut self) {
        // FIXME: not sure about this
        self.pc = self.pc.wrapping_add(1);
    }

    fn set_zero_and_negative_flags(&mut self, value: u8) {
        self.p.set(Flags::Z, value == 0);
        self.p.set(Flags::N, value & 0x80 != 0);
    }

    fn execute_read_write_instruction(&mut self, value: u8) -> u8 {
        match self.opcode.instruction {
            Instruction::Asl => self.asl(value),
            Instruction::Dec => self.dec(value),
            Instruction::Inc => self.inc(value),
            Instruction::Lsr => self.lsr(value),
            Instruction::Rol => self.rol(value),
            Instruction::Ror => self.ror(value),
            _ => todo!(),
        }
    }

    fn adc(&mut self) {
        let a = self.a as u16;
        let m = self.value0 as u16 + self.p.contains(Flags::C) as u16;
        let value = a + m;
        self.p
            .set(Flags::V, (a ^ value) & (m ^ value) & 0x0080 != 0);
        self.p.set(Flags::C, value & 0x0100 != 0);
        set_reg!(self, a, value as u8);
    }

    fn and(&mut self) {
        set_reg!(self, a, self.a & self.value0);
    }

    fn asl(&mut self, mut value: u8) -> u8 {
        let carry = value & 0x80;
        value = value << 1;
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, carry != 0);
        value
    }

    fn bit(&mut self) {
        let value = self.a & self.value0;
        self.set_zero_and_negative_flags(value);
    }

    fn cmp(&mut self) {
        let (value, overflow) = self.a.overflowing_sub(self.value0);
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, !overflow);
    }

    fn dec(&mut self, value: u8) -> u8 {
        let value = value.wrapping_sub(1);
        self.set_zero_and_negative_flags(value);
        value
    }

    fn eor(&mut self) {
        set_reg!(self, a, self.a ^ self.value0);
    }

    fn inc(&mut self, value: u8) -> u8 {
        let value = value.wrapping_add(1);
        self.set_zero_and_negative_flags(value);
        value
    }

    fn lda(&mut self) {
        set_reg!(self, a, self.value0);
    }

    fn ldx(&mut self) {
        set_reg!(self, x, self.value0);
    }

    fn ldy(&mut self) {
        set_reg!(self, y, self.value0);
    }

    fn lsr(&mut self, mut value: u8) -> u8 {
        let carry = value & 0x01;
        value = value >> 1;
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, carry != 0);
        value
    }

    fn ora(&mut self) {
        set_reg!(self, a, self.a | self.value0);
    }

    fn rol(&mut self, mut value: u8) -> u8 {
        let new_carry = value & 0x80;
        let old_carry = self.p.contains(Flags::C) as u8;
        value = (value << 1) | old_carry;
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, new_carry != 0);
        value
    }

    fn ror(&mut self, mut value: u8) -> u8 {
        let new_carry = value & 0x01;
        let old_carry = self.p.contains(Flags::C) as u8;
        value = (old_carry << 7) | (value >> 1);
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, new_carry != 0);
        value
    }

    fn sbc(&mut self) {
        let a = self.a as u16;
        let m = self.value0 as u16 + 1 - (self.p.contains(Flags::C) as u16);
        let value = a.wrapping_sub(m);
        // overflow if result > 127 or < -128
        // positive - negative -> positive overflow
        // positive - positive -> no overflow
        // negative - negative -> no overflow
        // negative - positive -> negative overflow
        //
        // overflow if (positive - negative -> negative) || (negative - positive -> positive)
        //
        // which can be translated to:
        // ((a & !m & !value) | (!a & m & value)) & 0x0080
        //
        // which can be simplified to:
        // (a ^ m) & (a ^ value) & 0x0080
        self.p.set(Flags::V, (a ^ m) & (a ^ value) & 0x0080 != 0);
        self.p.set(Flags::C, value & 0x0100 == 0);
        set_reg!(self, a, value as u8);
    }
}

