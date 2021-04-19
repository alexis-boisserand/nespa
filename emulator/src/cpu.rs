use bitflags::bitflags;
use num_traits::FromPrimitive;

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
struct OpCode(u8);

#[derive(Debug, Copy, Clone, num_derive::FromPrimitive)]
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

impl From<OpCode> for Instruction {
    fn from(opcode: OpCode) -> Self {
        // instructions are of the form aaabbbcc
        // where the combination of aaa and cc determine the opcode
        // and bbb the addressing mode
        let aaa = opcode.0 >> 5;
        let cc = opcode.0 & 0x3;
        let instruction = (cc << 3) | aaa;
        Instruction::from_u8(instruction).expect("invalid instruction")
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
}

impl From<OpCode> for AddressingMode {
    fn from(opcode: OpCode) -> Self {
        let cc = opcode.0 & 0x3;
        let bbb = (opcode.0 >> 2) & 0x7;

        match cc {
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
            0x10 => match bbb {
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
    ZeroPage,
    ZeroPageX,
    Absolute,
    PageCrossing,
    IndirectX0,
    IndirectX1,
    IndirectX2,
    IndirectY0,
    IndirectY1,
    Instruction,
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
            opcode: OpCode(0),
            value0: 0,
            value1: 0,
        }
    }

    pub fn tick(&mut self) {
        self.state = match self.state {
            CpuState::FetchOpCode => self.fetch_opcode(),
            CpuState::FetchValue0 => {
                self.value0 = self.read_mem(self.pc);
                self.increment_pc();
                match AddressingMode::from(self.opcode) {
                    AddressingMode::IndirectX => CpuState::IndirectX0,
                    AddressingMode::Zeropage => CpuState::ZeroPage,
                    AddressingMode::Immediate => CpuState::Instruction,
                    AddressingMode::Absolute => CpuState::FetchValue1(None),
                    AddressingMode::IndirectY => CpuState::IndirectY0,
                    AddressingMode::ZeroPageX => CpuState::ZeroPageX,
                    AddressingMode::AbsoluteY => CpuState::FetchValue1(Some(self.y)),
                    AddressingMode::AbsoluteX => CpuState::FetchValue1(Some(self.x)),
                    _ => todo!(),
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
                            CpuState::Absolute
                        }
                    }
                    None => CpuState::Absolute,
                }
            }
            CpuState::ZeroPage => {
                self.value0 = self.read_mem(self.value0 as u16);
                CpuState::Instruction
            }
            CpuState::ZeroPageX => {
                self.value0 = self.value0.wrapping_add(self.x);
                CpuState::ZeroPage
            }
            CpuState::PageCrossing => {
                self.value1 = self.value1.wrapping_add(1);
                CpuState::Absolute
            }
            CpuState::Absolute => {
                let address = (self.value1 as u16) << 8 | self.value0 as u16;
                self.value0 = self.read_mem(address);
                CpuState::Instruction
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
                CpuState::Absolute
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
                    CpuState::Absolute
                }
            }
            CpuState::Instruction => {
                match Instruction::from(self.opcode) {
                    Instruction::Adc => self.adc(),
                    Instruction::And => self.and(),
                    Instruction::Eor => self.eor(),
                    Instruction::Ora => self.ora(),
                    Instruction::Sbc => self.sbc(),
                    _ => todo!(),
                };
                self.fetch_opcode()
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
        self.opcode = OpCode(self.read_mem(self.pc));
        self.increment_pc();
        CpuState::FetchValue0
    }

    fn increment_pc(&mut self) {
        // FIXME: not sure about this
        self.pc = self.pc.wrapping_add(1);
    }

    fn set_zero_and_negative_flags(&mut self) {
        self.p.set(Flags::Z, self.a == 0);
        self.p.set(Flags::N, self.a & 0x80 != 0);
    }

    fn adc(&mut self) {
        let a = self.a as u16;
        let m = self.value0 as u16 + self.p.contains(Flags::C) as u16;
        let value = a + m;
        self.a = value as u8;
        self.p
            .set(Flags::V, (a ^ value) & (m ^ value) & 0x0080 != 0);
        self.p.set(Flags::C, value & 0x0100 != 0);
        self.set_zero_and_negative_flags();
    }

    fn and(&mut self) {
        self.a = self.a & self.value0;
        self.set_zero_and_negative_flags();
    }

    fn eor(&mut self) {
        self.a = self.a ^ self.value0;
        self.set_zero_and_negative_flags();
    }

    fn ora(&mut self) {
        self.a = self.a | self.value0;
        self.set_zero_and_negative_flags();
    }

    fn sbc(&mut self) {
        let a = self.a as u16;
        let m = self.value0 as u16 + 1 - (self.p.contains(Flags::C) as u16);
        let value = a.wrapping_sub(m);
        self.a = value as u8;
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
        self.p.set(
            Flags::V,
            (a ^ m) & (a ^ value) & 0x0080 != 0
        );
        self.p.set(Flags::C, value & 0x0100 == 0);
        self.set_zero_and_negative_flags();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const RAM_CODE_START: u16 = 0x400;

    fn setup(instructions: &[u8]) -> Cpu {
        let mut cpu = Cpu::new();
        cpu.write_mem_u16(RESET_VECTOR, RAM_CODE_START);
        instructions.iter().enumerate().for_each(|(index, value)| {
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
}
