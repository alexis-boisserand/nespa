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
    None,
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
    addressing_mode: AddressingMode,
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
            addressing_mode: AddressingMode::None,
            opcode: OpCode(0),
            value0: 0,
            value1: 0,
        }
    }

    pub fn tick(&mut self) {
        match self.state {
            CpuState::FetchOpCode => {
                self.fetch_opcode();
            }
            CpuState::FetchValue0 => {
                self.value0 = self.read_mem(self.pc);
                // FIXME: what if PC wraps?
                self.pc += 1;
                self.addressing_mode = AddressingMode::from(self.opcode);
                self.state = match self.addressing_mode {
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::Zeropage => CpuState::ZeroPage,
                    AddressingMode::Immediate => CpuState::Instruction,
                    AddressingMode::Absolute => CpuState::FetchValue1(None),
                    AddressingMode::IndirectY => todo!(),
                    AddressingMode::ZeroPageX => CpuState::ZeroPageX,
                    AddressingMode::AbsoluteY => CpuState::FetchValue1(Some(self.y)),
                    AddressingMode::AbsoluteX => CpuState::FetchValue1(Some(self.x)),
                    _ => todo!(),
                };
            }
            CpuState::FetchValue1(index) => {
                self.value1 = self.read_mem(self.pc);
                self.pc += 1;
                self.state = match index {
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
                };
            }
            CpuState::ZeroPage => {
                self.value0 = self.read_mem(self.value0 as u16);
                self.state = CpuState::Instruction;
            }
            CpuState::ZeroPageX => {
                self.value0 = self.value0.wrapping_add(self.x);
                self.state = CpuState::ZeroPage;
            }
            CpuState::PageCrossing => {
                self.value1 = self.value1.wrapping_add(1);
                self.state = CpuState::Absolute;
            }
            CpuState::Absolute => {
                let address = self.value1 as u16 >> 8 | self.value0 as u16;
                self.value0 = self.read_mem(address);
                self.state = CpuState::Instruction;
            }
            CpuState::Instruction => {
                match Instruction::from(self.opcode) {
                    Instruction::And => self.and(),
                    _ => todo!(),
                };
            }
        }
    }

    pub fn reset(&mut self) {
        // TODO initialize other registers
        self.pc = self.read_mem_u16(RESET_VECTOR);
        self.state = CpuState::FetchOpCode;
    }

    fn fetch_opcode(&mut self) {
        self.opcode = OpCode(self.read_mem(self.pc));
        // FIXME: what if PC wraps?
        self.pc += 1;
        self.state = CpuState::FetchValue0;
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

    fn set_zero_and_negative_flags(&mut self) {
        self.p.set(Flags::Z, self.a == 0);
        self.p.set(Flags::N, self.a & 0x80 != 0);
    }

    fn and(&mut self) {
        self.a = self.a & self.value0;
        self.set_zero_and_negative_flags();
        self.fetch_opcode();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const RAM_CODE_START: u16 = 0x400;
    #[test]
    fn and() {
        let mut cpu = Cpu::new();
        cpu.a = 0xff;
        cpu.write_mem_u16(RESET_VECTOR, RAM_CODE_START);
        let instructions = [0x29, 0xaa, 0x29, 0x55, 0x25, 0x16];
        instructions.iter().enumerate().for_each(|(index, value)| {
            cpu.write_mem(RAM_CODE_START + index as u16, *value);
        });
        cpu.reset();
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

        cpu.a = 0x0f;
        cpu.write_mem(0x16, 0x2);
        cpu.tick(); // fetch address
        cpu.tick(); // fetch operand from memory
        assert_ne!(cpu.a, 0x02);
        cpu.tick(); // execute and fetch next opcode
        assert_eq!(cpu.a, 0x02);
        assert!(!cpu.p.contains(Flags::N));
        assert!(!cpu.p.contains(Flags::Z));
    }
}
