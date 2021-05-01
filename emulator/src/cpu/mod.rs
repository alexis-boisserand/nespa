mod opcodes;
#[cfg(test)]
mod tests;

use self::opcodes::{AddressingMode, Instruction, OpCode};
use bitflags::bitflags;

macro_rules! set_reg {
    ($self:ident, $field:ident, $value:expr) => {
        $self.set_zero_and_negative_flags($value);
        $self.$field = $value;
    };
}

const STACK_ADDRESS_OFFSET: u16 = 0x0100;
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

#[derive(Debug)]
enum CpuState {
    FetchOpCode,
    FetchValue,
    Absolute(Option<u8>),
    Accumulator(opcodes::ReadWriteInstruction),
    ReadOrWrite,
    ZeroPageX,
    PageCrossing,
    IndirectX0,
    IndirectX1,
    IndirectX2,
    IndirectY0,
    IndirectY1,
    ReadInstruction(opcodes::ReadInstruction),
    ReadWriteInstruction(opcodes::ReadWriteInstruction, u16),
    BranchInstruction0(opcodes::BranchInstruction),
    ImpliedInstruction(opcodes::ImpliedInstruction),
    PushInstruction(opcodes::PushInstruction),
    PullInstruction0(opcodes::PullInstruction),
    PullInstruction1(opcodes::PullInstruction),
    BranchInstruction1(bool),
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
            p: Flags::from_bits_truncate(P_INIT_VALUE),
            mem: [0; 0xFFFF],
            state: CpuState::FetchOpCode,
            // actual initial values don't matter the next 3 fields
            opcode: OpCode::from(0x69),
            value0: 0,
            value1: 0,
        }
    }

    pub fn tick(&mut self) {
        self.state = match self.state {
            CpuState::FetchOpCode => {
                self.fetch_opcode();
                self.increment_pc();
                CpuState::FetchValue
            }
            CpuState::FetchValue => {
                self.value0 = self.read_mem(self.pc);
                self.value1 = 0;
                //self.increment_pc(); // in the case of single byte instruction, the following byte is read and discarded
                match self.opcode.addressing_mode {
                    AddressingMode::Accumulator | AddressingMode::Implied => {}
                    _ => self.increment_pc(),
                }
                match self.opcode.addressing_mode {
                    AddressingMode::Accumulator => {
                        if let Instruction::ReadWrite(instruction) = self.opcode.instruction {
                            CpuState::Accumulator(instruction)
                        } else {
                            unreachable!("only read write instructions support the accumulator addressing mode")
                        }
                    }
                    AddressingMode::IndirectX => CpuState::IndirectX0,
                    AddressingMode::ZeroPage => CpuState::ReadOrWrite,
                    AddressingMode::Immediate => {
                        if let Instruction::Read(instruction) = self.opcode.instruction {
                            CpuState::ReadInstruction(instruction)
                        } else {
                            unreachable!(
                                "only read instructions support the immediate addressing mode"
                            )
                        }
                    }
                    AddressingMode::Absolute => CpuState::Absolute(None),
                    AddressingMode::IndirectY => CpuState::IndirectY0,
                    AddressingMode::ZeroPageX => CpuState::ZeroPageX,
                    AddressingMode::ZeroPageY => unimplemented!(),
                    AddressingMode::AbsoluteY => CpuState::Absolute(Some(self.y)),
                    AddressingMode::AbsoluteX => CpuState::Absolute(Some(self.x)),
                    AddressingMode::Implied => {
                        if let Instruction::Implied(instruction) = self.opcode.instruction {
                            CpuState::ImpliedInstruction(instruction)
                        } else if let Instruction::Push(instruction) = self.opcode.instruction {
                            CpuState::PushInstruction(instruction)
                        } else if let Instruction::Pull(instruction) = self.opcode.instruction {
                            CpuState::PullInstruction0(instruction)
                        } else {
                            unreachable!()
                        }
                    }
                    AddressingMode::Indirect => unimplemented!(),
                    AddressingMode::Relative => {
                        if let Instruction::Branch(instruction) = self.opcode.instruction {
                            CpuState::BranchInstruction0(instruction)
                        } else {
                            unreachable!(
                                "only read instructions support the immediate addressing mode"
                            )
                        }
                    }
                }
            }
            CpuState::Absolute(index) => {
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
            CpuState::Accumulator(instruction) => {
                self.a = self.execute_read_write_instruction(instruction, self.a);
                self.fetch_opcode();
                self.increment_pc();
                CpuState::FetchValue
            }
            CpuState::ReadOrWrite => {
                let address = (self.value1 as u16) << 8 | self.value0 as u16;
                match self.opcode.instruction {
                    Instruction::Read(instruction) => {
                        self.value0 = self.read_mem(address);
                        CpuState::ReadInstruction(instruction)
                    }
                    Instruction::ReadWrite(instruction) => {
                        self.value0 = self.read_mem(address);
                        CpuState::ReadWriteInstruction(instruction, address)
                    }
                    Instruction::Write(instruction) => {
                        let value = match instruction {
                            opcodes::WriteInstruction::Sta => self.a,
                            opcodes::WriteInstruction::Stx => self.x,
                            opcodes::WriteInstruction::Sty => self.y,
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
            CpuState::ReadInstruction(instruction) => {
                match instruction {
                    opcodes::ReadInstruction::Adc => self.adc(),
                    opcodes::ReadInstruction::And => self.and(),
                    opcodes::ReadInstruction::Bit => self.bit(),
                    opcodes::ReadInstruction::Cmp => self.cmp(),
                    opcodes::ReadInstruction::Eor => self.eor(),
                    opcodes::ReadInstruction::Lda => self.lda(),
                    opcodes::ReadInstruction::Ldx => self.ldx(),
                    opcodes::ReadInstruction::Ldy => self.ldy(),
                    opcodes::ReadInstruction::Ora => self.ora(),
                    opcodes::ReadInstruction::Sbc => self.sbc(),
                    opcodes::ReadInstruction::Cpx => self.cpx(),
                    opcodes::ReadInstruction::Cpy => self.cpy(),
                };
                self.fetch_opcode();
                self.increment_pc();
                CpuState::FetchValue
            }
            CpuState::ReadWriteInstruction(instruction, address) => {
                // in theory, at this point, self.value0 is written to address
                // right before executing the instruction
                self.value0 = self.execute_read_write_instruction(instruction, self.value0);
                CpuState::WriteBack(address)
            }
            CpuState::WriteBack(address) => {
                self.write_mem(address, self.value0);
                CpuState::FetchOpCode
            }
            CpuState::BranchInstruction0(instruction) => {
                self.fetch_opcode();
                let condition_fulfilled: bool = match instruction {
                    opcodes::BranchInstruction::Bcc => self.bcc(),
                    opcodes::BranchInstruction::Bcs => self.bcs(),
                    opcodes::BranchInstruction::Beq => self.beq(),
                    opcodes::BranchInstruction::Bmi => self.bmi(),
                    opcodes::BranchInstruction::Bne => self.bne(),
                    opcodes::BranchInstruction::Bpl => self.bpl(),
                    opcodes::BranchInstruction::Bvc => self.bvc(),
                    opcodes::BranchInstruction::Bvs => self.bvs(),
                };
                if condition_fulfilled {
                    let pcl = (self.pc & 0xFF) as u8;
                    let offset = self.value0 as i8;
                    let offset_positive = offset.is_positive();
                    let (value, pagebound_crossed) = if offset_positive {
                        pcl.overflowing_add(self.value0)
                    } else {
                        pcl.overflowing_sub(offset.unsigned_abs())
                    };
                    self.pc = (self.pc & 0xFF00) | value as u16;
                    if pagebound_crossed {
                        CpuState::BranchInstruction1(offset_positive)
                    } else {
                        CpuState::FetchOpCode
                    }
                } else {
                    self.increment_pc();
                    CpuState::FetchValue
                }
            }
            CpuState::BranchInstruction1(positive) => {
                self.fetch_opcode();
                let mut pch = (self.pc >> 8) as u8;
                pch = if positive {
                    pch.wrapping_add(1)
                } else {
                    pch.wrapping_sub(1)
                };
                self.pc = (pch as u16) << 8 | (self.pc & 0xFF);
                CpuState::FetchOpCode
            }
            CpuState::ImpliedInstruction(instruction) => {
                match instruction {
                    opcodes::ImpliedInstruction::Clc => self.clc(),
                    opcodes::ImpliedInstruction::Cld => self.cld(),
                    opcodes::ImpliedInstruction::Cli => self.cli(),
                    opcodes::ImpliedInstruction::Clv => self.clv(),
                    opcodes::ImpliedInstruction::Dex => self.dex(),
                    opcodes::ImpliedInstruction::Dey => self.dey(),
                    opcodes::ImpliedInstruction::Iny => self.iny(),
                    opcodes::ImpliedInstruction::Inx => self.inx(),
                    opcodes::ImpliedInstruction::Nop => {}
                    opcodes::ImpliedInstruction::Sec => self.sec(),
                    opcodes::ImpliedInstruction::Sed => self.sed(),
                    opcodes::ImpliedInstruction::Sei => self.sei(),
                    opcodes::ImpliedInstruction::Tax => self.tax(),
                    opcodes::ImpliedInstruction::Tay => self.tay(),
                    opcodes::ImpliedInstruction::Tsx => self.tsx(),
                    opcodes::ImpliedInstruction::Txa => self.txa(),
                    opcodes::ImpliedInstruction::Txs => self.txs(),
                    opcodes::ImpliedInstruction::Tya => self.tya(),
                }
                self.fetch_opcode();
                self.increment_pc();
                CpuState::FetchValue
            }
            CpuState::PushInstruction(instruction) => {
                match instruction {
                    opcodes::PushInstruction::Pha => self.pha(),
                    opcodes::PushInstruction::Php => self.php(),
                }
                CpuState::FetchOpCode
            }
            CpuState::PullInstruction0(instruction) => {
                self.s = self.s.wrapping_add(1);
                CpuState::PullInstruction1(instruction)
            }
            CpuState::PullInstruction1(instruction) => {
                match instruction {
                    opcodes::PullInstruction::Pla => self.pla(),
                    opcodes::PullInstruction::Plp => self.plp(),
                }
                CpuState::FetchOpCode
            }
        };
    }

    pub fn reset(&mut self) {
        // TODO initialize other registers
        self.p = Flags::from_bits_truncate(P_INIT_VALUE);
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

    #[cfg(test)]
    fn write_mem_u16(&mut self, address: u16, value: u16) {
        let value = value.to_le_bytes();
        let address = address as usize;
        &self.mem[address..address + 2]
            .iter_mut()
            .zip(value.iter())
            .for_each(|(dest, src)| *dest = *src);
    }

    #[cfg(test)]
    fn stack_peek(&mut self) -> u8 {
        // 6502 uses a descending (grows by decrementing address)
        // empty (stack points to the next value that will be stored) stack
        // stack is in RAM in the address range [0x0100;0x01ff]
        // stack pointer is only 8 bits
        // which means the current stack address is actually 0x0100 + s
        let address = STACK_ADDRESS_OFFSET + self.s.wrapping_add(1) as u16;
        self.read_mem(address)
    }

    fn stack_pull(&mut self) -> u8 {
        // note: it is assumed that s has been previously incremented
        let address = STACK_ADDRESS_OFFSET + self.s as u16;
        self.read_mem(address)
    }

    fn stack_push(&mut self, value: u8) {
        let address = STACK_ADDRESS_OFFSET + self.s as u16;
        self.write_mem(address, value);
        self.s = self.s.wrapping_sub(1);
    }

    fn fetch_opcode(&mut self) {
        self.opcode = OpCode::from(self.read_mem(self.pc));
    }

    fn increment_pc(&mut self) {
        // FIXME: not sure about this
        self.pc = self.pc.wrapping_add(1);
    }

    fn set_zero_and_negative_flags(&mut self, value: u8) {
        self.p.set(Flags::Z, value == 0);
        self.p.set(Flags::N, value & 0x80 != 0);
    }

    fn execute_read_write_instruction(
        &mut self,
        instruction: opcodes::ReadWriteInstruction,
        value: u8,
    ) -> u8 {
        match instruction {
            opcodes::ReadWriteInstruction::Asl => self.asl(value),
            opcodes::ReadWriteInstruction::Dec => self.dec(value),
            opcodes::ReadWriteInstruction::Inc => self.inc(value),
            opcodes::ReadWriteInstruction::Lsr => self.lsr(value),
            opcodes::ReadWriteInstruction::Rol => self.rol(value),
            opcodes::ReadWriteInstruction::Ror => self.ror(value),
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

    fn bcc(&mut self) -> bool {
        !self.p.contains(Flags::C)
    }

    fn bcs(&mut self) -> bool {
        self.p.contains(Flags::C)
    }

    fn beq(&mut self) -> bool {
        self.p.contains(Flags::Z)
    }

    fn bit(&mut self) {
        let value = self.a & self.value0;
        self.set_zero_and_negative_flags(value);
    }

    fn bmi(&mut self) -> bool {
        self.p.contains(Flags::N)
    }

    fn bne(&mut self) -> bool {
        !self.p.contains(Flags::Z)
    }

    fn bpl(&mut self) -> bool {
        !self.p.contains(Flags::N)
    }

    fn bvc(&mut self) -> bool {
        !self.p.contains(Flags::V)
    }

    fn bvs(&mut self) -> bool {
        self.p.contains(Flags::V)
    }

    fn clc(&mut self) {
        self.p.set(Flags::C, false);
    }

    fn cld(&mut self) {
        self.p.set(Flags::D, false);
    }

    fn cli(&mut self) {
        self.p.set(Flags::I, false);
    }

    fn clv(&mut self) {
        self.p.set(Flags::V, false);
    }

    fn cmp(&mut self) {
        let (value, overflow) = self.a.overflowing_sub(self.value0);
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, !overflow);
    }

    fn cpx(&mut self) {
        let (value, overflow) = self.x.overflowing_sub(self.value0);
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, !overflow);
    }

    fn cpy(&mut self) {
        let (value, overflow) = self.y.overflowing_sub(self.value0);
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, !overflow);
    }

    fn dec(&mut self, value: u8) -> u8 {
        let value = value.wrapping_sub(1);
        self.set_zero_and_negative_flags(value);
        value
    }

    fn dex(&mut self) {
        self.x = self.dec(self.x);
    }

    fn dey(&mut self) {
        self.y = self.dec(self.y);
    }

    fn eor(&mut self) {
        set_reg!(self, a, self.a ^ self.value0);
    }

    fn inc(&mut self, value: u8) -> u8 {
        let value = value.wrapping_add(1);
        self.set_zero_and_negative_flags(value);
        value
    }

    fn inx(&mut self) {
        self.x = self.inc(self.x);
    }

    fn iny(&mut self) {
        self.y = self.inc(self.y);
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

    fn pha(&mut self) {
        self.stack_push(self.a);
    }

    fn php(&mut self) {
        self.stack_push(self.p.bits());
    }

    fn pla(&mut self) {
        self.a = self.stack_pull();
        self.set_zero_and_negative_flags(self.a);
    }

    fn plp(&mut self) {
        self.p = Flags::from_bits_truncate(self.stack_pull());
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

    fn sec(&mut self) {
        self.p.set(Flags::C, true);
    }

    fn sed(&mut self) {
        self.p.set(Flags::D, true);
    }

    fn sei(&mut self) {
        self.p.set(Flags::I, true);
    }

    fn tax(&mut self) {
        set_reg!(self, x, self.a);
    }

    fn tay(&mut self) {
        set_reg!(self, y, self.a);
    }

    fn tsx(&mut self) {
        set_reg!(self, x, self.s);
    }

    fn txa(&mut self) {
        set_reg!(self, a, self.x);
    }

    fn txs(&mut self) {
        self.s = self.x;
    }

    fn tya(&mut self) {
        set_reg!(self, a, self.y);
    }
}
