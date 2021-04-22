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

#[cfg(test)]
mod tests {
    use super::*;
    use core::iter;
    const RAM_CODE_START: u16 = 0x400;

    fn setup(instructions: &[u8]) -> Cpu {
        let mut cpu = Cpu::new();
        cpu.write_mem_u16(RESET_VECTOR, RAM_CODE_START);
        instructions
            .iter()
            .chain(iter::once(&0x69)) // just add a valid opcode for the test not to panic
            // when it encounters an invalid one
            .enumerate()
            .for_each(|(index, value)| {
                cpu.write_mem(RAM_CODE_START + index as u16, *value);
            });
        cpu.reset();
        cpu
    }

    #[test]
    fn adc() {
        // test Z, N and C flags
        let mut cpu = setup(&[
            0x69, 0x00, // ADC #$00
            0x69, 0xe0, // ADC #$e0
            0x69, 0x20, // ADC #$20
            0x69, 0xff, // ADC #$ff
        ]);
        cpu.a = 0x00;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(!cpu.p.contains(Flags::C));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xe0);
        assert!(!cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(!cpu.p.contains(Flags::C));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(cpu.p.contains(Flags::C));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(cpu.p.contains(Flags::C));

        // test V flag
        let mut cpu = setup(&[
            0x69, 0x44, // ADC #$44 with a set to 0x42
            0x69, 0xd0, // ADC #$d0 with a set to 0x90
        ]);
        cpu.a = 0x42;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x86);
        assert!(!cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::V));
        assert!(!cpu.p.contains(Flags::C));

        cpu.a = 0x90;
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x60);
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::V));
        assert!(cpu.p.contains(Flags::C));
    }

    #[test]
    fn and_immediate() {
        let mut cpu = setup(&[
            0x29, 0xaa, // AND #$aa
            0x29, 0x55, // AND #$55
        ]);
        cpu.a = 0xff;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xaa);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
                    // value shouldn't have changed at this point
        assert_ne!(cpu.a, 0x00);
        cpu.tick(); // execute and fetch next opcode
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
    }

    #[test]
    fn and_zero_page() {
        let mut cpu = setup(&[
            0x25, 0x16, // AND $16
        ]);
        cpu.a = 0xff;
        cpu.write_mem(0x16, 0x55);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x55);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn and_zero_page_x() {
        let mut cpu = setup(&[
            0x35, 0x16, // AND $16,X
        ]);
        cpu.a = 0xff;
        cpu.x = 0x02;
        cpu.write_mem(0x18, 0x53);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address
        cpu.tick(); // add X to the address
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x53);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn and_absolute() {
        let mut cpu = setup(&[
            0x2D, 0x16, 0x22, // AND $2216
        ]);
        cpu.a = 0xff;
        cpu.write_mem(0x2216, 0xf5);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address low byte
        cpu.tick(); // fetch address high byte
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xf5);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn and_absolute_y() {
        let mut cpu = setup(&[
            0x39, 0x16, 0x22, // AND $2216,Y
            0x39, 0x16, 0x22, // AND $2216,Y
        ]);

        // no page bound crossing
        cpu.a = 0xff;
        cpu.y = 0x04;
        cpu.write_mem(0x221a, 0x65);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address low byte
        cpu.tick(); // fetch address high byte and add y to the low address byte
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x65);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        // page bound crossing
        cpu.a = 0xff;
        cpu.y = 0xf0;
        cpu.write_mem(0x2306, 0xf3);
        cpu.tick(); // fetch address low byte
        cpu.tick(); // fetch address high byte and add y to the low address byte, page bound cross detected
        cpu.tick(); // add 1 to the address high byte
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xf3);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn and_absolute_x() {
        let mut cpu = setup(&[
            0x3D, 0x16, 0x22, // AND $2216,X
            0x3D, 0x16, 0x22, // AND $2216,X
        ]);

        // no page bound crossing
        cpu.a = 0xff;
        cpu.x = 0x04;
        cpu.write_mem(0x221a, 0x65);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address low byte
        cpu.tick(); // fetch address high byte and add x to the low address byte
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x65);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        // page bound crossing
        cpu.a = 0xff;
        cpu.x = 0xf0;
        cpu.write_mem(0x2306, 0xf3);
        cpu.tick(); // fetch address low byte
        cpu.tick(); // fetch address high byte and add x to the low address byte, page bound cross detected
        cpu.tick(); // add 1 to the address high byte
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xf3);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn and_indirect_x() {
        let mut cpu = setup(&[
            0x21, 0x16, // AND ($16,X)
        ]);

        cpu.a = 0xff;
        cpu.x = 0x04;
        cpu.write_mem_u16(0x1a, 0x2442);
        cpu.write_mem(0x2442, 0x32);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address's address
        cpu.tick(); // add x to address's address
        cpu.tick(); // fetch low byte address and increment address's address at the same time
        cpu.tick(); // fetch high byte address
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x32);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn and_indirect_y() {
        let mut cpu = setup(&[
            0x31, 0x26, // AND ($16),Y
            0x31, 0x26, // AND ($16),Y
        ]);

        // no page bound crossing
        cpu.a = 0xff;
        cpu.y = 0x04;
        cpu.write_mem_u16(0x26, 0x2244);
        cpu.write_mem(0x2248, 0x21);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address's address
        cpu.tick(); // fetch address low byte
        cpu.tick(); // fetch address high byte and add x to the low address byte
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x21);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        // page bound crossing
        cpu.a = 0xff;
        cpu.y = 0x06;
        cpu.write_mem_u16(0x26, 0x22fe);
        cpu.write_mem(0x2304, 0xf4);
        cpu.tick(); // fetch address's address
        cpu.tick(); // fetch address low byte
        cpu.tick(); // fetch address high byte and add x to the low address byte, page bound cross detected
        cpu.tick(); // add 1 to the address high byte
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xf4);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn asl() {
        let mut cpu = setup(&[
            0x0A, 0x43, // ASL A // next byte is discarded
            0x06, 0x44, // ASL $44
            0x16, 0x64, // ASL $64,X
        ]);
        cpu.a = 0x80;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand (and throw it away)
        assert_eq!(cpu.a, 0x80);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::C));

        cpu.write_mem(0x44, 0x42);
        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x44), 0x42);
        cpu.tick(); // write result back to address
        assert_eq!(cpu.read_mem(0x44), 0x84);
        cpu.tick(); // fetch next opcode
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));

        cpu.x = 0x02;
        cpu.write_mem(0x66, 0x28);
        cpu.tick(); // fetch address
        cpu.tick(); // add X to the address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x66), 0x28);
        cpu.tick(); // write result back
        assert_eq!(cpu.read_mem(0x66), 0x50);
        cpu.tick(); // fetch next opcode
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));
    }

    #[test]
    fn bit() {
        let mut cpu = setup(&[
            0x24, 0x16, // BIT $16
            0x24, 0x16, // BIT $16
            0x24, 0x16, // BIT $16
        ]);
        cpu.a = 0xff;
        cpu.write_mem(0x16, 0x80);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xff); // values doesn't change
        assert_eq!(cpu.read_mem(0x16), 0x80); // value doesn't change
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.write_mem(0x16, 0x08);
        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.a = 0x40;
        cpu.write_mem(0x16, 0x02);
        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
    }

    #[test]
    fn cmp() {
        let mut cpu = setup(&[
            0xC9, 0x43, // CMP #$43
            0xC9, 0x54, // CMP #$54
            0xC9, 0x20, // CMP #$20
        ]);
        cpu.a = 0x43;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x43);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::C));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x43);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x43);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::C));
    }

    #[test]
    fn dec() {
        let mut cpu = setup(&[
            0xC6, 0x43, // DEC $43
            0xC6, 0x43, // DEC $43
        ]);

        cpu.write_mem(0x43, 0x01);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x43), 0x01);
        cpu.tick(); // write result back to address
        assert_eq!(cpu.read_mem(0x43), 0x00);
        cpu.tick(); // fetch next opcode
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x43), 0x00);
        cpu.tick(); // write result back to address
        assert_eq!(cpu.read_mem(0x43), 0xff);
        cpu.tick(); // fetch next opcode
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn inc() {
        let mut cpu = setup(&[
            0xE6, 0x43, // INC $43
            0xE6, 0x43, // INC $43
            0xE6, 0x43, // INC $43
        ]);

        cpu.write_mem(0x43, 0xfe);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x43), 0xfe);
        cpu.tick(); // write result back to address
        assert_eq!(cpu.read_mem(0x43), 0xff);
        cpu.tick(); // fetch next opcode
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x43), 0xff);
        cpu.tick(); // write result back to address
        assert_eq!(cpu.read_mem(0x43), 0x00);
        cpu.tick(); // fetch next opcode
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x43), 0x00);
        cpu.tick(); // write result back to address
        assert_eq!(cpu.read_mem(0x43), 0x01);
        cpu.tick(); // fetch next opcode
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn eor() {
        let mut cpu = setup(&[
            0x49, 0xaa, // EOR #$aa
            0x49, 0xaa, // EOR #$aa
        ]);
        cpu.a = 0x00;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xaa);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and fetch next opcode
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
    }

    #[test]
    fn lda() {
        let mut cpu = setup(&[
            0xA9, 0x00, // LDA $#00
            0xA9, 0x81, // LDA $#81
            0xA9, 0x23, // LDA $#23
        ]);
        cpu.a = 0xff;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        assert_eq!(cpu.a, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x81);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x23);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn ldx() {
        let mut cpu = setup(&[
            0xA2, 0x00, // LDX $#00
            0xA2, 0x81, // LDX $#81
            0xA2, 0x23, // LDX $#23
        ]);
        cpu.x = 0xff;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        assert_eq!(cpu.x, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.x, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.x, 0x81);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.x, 0x23);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn ldy() {
        let mut cpu = setup(&[
            0xA0, 0x00, // LDY $#00
            0xA0, 0x81, // LDY $#81
            0xA0, 0x23, // LDY $#23
        ]);
        cpu.y = 0xff;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        assert_eq!(cpu.y, 0xff);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.y, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.y, 0x81);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.y, 0x23);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn lsr() {
        let mut cpu = setup(&[
            0x4A, 0x43, // LSR A // next byte is discarded
            0x4A, 0x44, // LSR A
            0x4A, 0x64, // LSR A
        ]);
        cpu.a = 0x01;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand (and throw it away)
        assert_eq!(cpu.a, 0x01);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::C));

        cpu.tick(); // fetch operand (and throw it away)
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));

        cpu.a = 0x44;
        cpu.tick(); // fetch operand (and throw it away)
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x22);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));
    }
    #[test]
    fn ora() {
        let mut cpu = setup(&[
            0x09, 0x00, // ORA #$00
            0x09, 0x55, // ORA #$55
            0x09, 0xaa, // ORA #$aa
        ]);
        cpu.a = 0x00;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and fetch next opcode
        assert_eq!(cpu.a, 0x55);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));

        cpu.tick(); // fetch operand
        cpu.tick(); // execute and fetch next opcode
        assert_eq!(cpu.a, 0xff);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }

    #[test]
    fn rol() {
        let mut cpu = setup(&[
            0x2A, 0x43, // ROL A // next byte is discarded
            0x26, 0x44, // ROL $44
            0x36, 0x64, // ROL $64,X
        ]);
        cpu.a = 0x80;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand (and throw it away)
        assert_eq!(cpu.a, 0x80);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::C));

        cpu.write_mem(0x44, 0x42);
        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x44), 0x42);
        cpu.tick(); // write result back to address
        assert_eq!(cpu.read_mem(0x44), 0x85);
        cpu.tick(); // fetch next opcode
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));

        cpu.x = 0x02;
        cpu.write_mem(0x66, 0x28);
        cpu.tick(); // fetch address
        cpu.tick(); // add X to the address
        cpu.tick(); // fetch operand
        cpu.tick(); // execute instruction
        assert_eq!(cpu.read_mem(0x66), 0x28);
        cpu.tick(); // write result back
        assert_eq!(cpu.read_mem(0x66), 0x50);
        cpu.tick(); // fetch next opcode
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));
    }

    #[test]
    fn ror() {
        let mut cpu = setup(&[
            0x6A, 0x43, // ROR A // next byte is discarded
            0x6A, 0x44, // ROR A
            0x6A, 0x64, // ROR A
        ]);
        cpu.a = 0x01;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand (and throw it away)
        assert_eq!(cpu.a, 0x01);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::C));

        cpu.tick(); // fetch operand (and throw it away)
        assert_eq!(cpu.a, 0x00);
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x80);
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));

        cpu.a = 0x44;
        cpu.tick(); // fetch operand (and throw it away)
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x22);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::C));
    }
    #[test]
    fn sbc() {
        // test Z, N and C flags
        let mut cpu = setup(&[
            0xe9, 0x00, // SBC #$00
            0xe9, 0x02, // SBC #$02 with a set to 0x0a
            0xe9, 0x30, // SBC #$20 with a set to 0x20
            // try 0x4521 - 0x4434 = 0xed
            0xe9, 0x34, // SBC #$34 with a set to 21
            0xe9, 0x44, // SBC #$44 with a set to 45
        ]);
        cpu.a = 0x00;
        cpu.p.set(Flags::C, true);
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(cpu.p.contains(Flags::C));

        cpu.a = 0x0a;
        cpu.p.set(Flags::C, true);
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x08);
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(cpu.p.contains(Flags::C));

        cpu.a = 0x20;
        cpu.p.set(Flags::C, true);
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xf0);
        assert!(!cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(!cpu.p.contains(Flags::C));

        cpu.a = 0x21;
        cpu.p.set(Flags::C, true);
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xed);
        assert!(!cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(!cpu.p.contains(Flags::C));

        cpu.a = 0x45;
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x00);
        assert!(cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::V));
        assert!(cpu.p.contains(Flags::C));

        // test V flag
        let mut cpu = setup(&[
            0xe9, 0xb0, // SBC #$b0 with a set to 0x50
            0xe9, 0x70, // SBC #$d0 with a set to 0xd0
        ]);
        cpu.p.set(Flags::C, true);
        cpu.a = 0x50;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0xa0);
        assert!(!cpu.p.contains(Flags::Z));
        assert!(cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::V));
        assert!(!cpu.p.contains(Flags::C));

        cpu.p.set(Flags::C, true);
        cpu.a = 0xd0;
        cpu.tick(); // fetch operand
        cpu.tick(); // execute and and fetch the next opcode at the same time
        assert_eq!(cpu.a, 0x60);
        assert!(!cpu.p.contains(Flags::Z));
        assert!(!cpu.p.contains(Flags::N));
        assert!(cpu.p.contains(Flags::V));
        assert!(cpu.p.contains(Flags::C));
    }

    #[test]
    fn sta() {
        let mut cpu = setup(&[
            0x85, 0x16, // STA $16
        ]);
        cpu.a = 0x32;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address
        cpu.tick(); // write register to address
        cpu.tick(); // fetch the next opcode
        assert_eq!(cpu.read_mem(0x0016), 0x32);
    }

    #[test]
    fn stx() {
        let mut cpu = setup(&[
            0x86, 0x16, // STX $16
        ]);
        cpu.x = 0x42;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address
        cpu.tick(); // write register to address
        cpu.tick(); // fetch the next opcode
        assert_eq!(cpu.read_mem(0x0016), 0x42);
    }

    #[test]
    fn sty() {
        let mut cpu = setup(&[
            0x84, 0x16, // STY $16
        ]);
        cpu.y = 0x78;
        cpu.tick(); // fetch opcode
        cpu.tick(); // fetch address
        cpu.tick(); // write register to address
        cpu.tick(); // fetch the next opcode
        assert_eq!(cpu.read_mem(0x0016), 0x78);
    }
}
