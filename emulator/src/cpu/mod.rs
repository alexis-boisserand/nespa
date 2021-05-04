mod opcodes;
#[cfg(test)]
mod tests;

use self::opcodes::*;
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
const INTERRUPT_VECTOR: u16 = 0xFFFE;

bitflags! {
    struct Flags: u8 {
        const C = 0x01;
        const Z = 0x02;
        const I = 0x04;
        const D = 0x10;
        const B = 0x20;
        const V = 0x40;
        const N = 0x80;
    }
}

#[derive(Debug)]
enum CpuState {
    FetchOpCode,
    FetchValue(OpCode),
    Absolute(Instruction, u8, Option<u8>),
    PageCrossing(Instruction, u16),
    Accumulator(ReadWriteInstruction),
    ZeroPageIndexed(Instruction, u8, u8),
    IndirectX0(Instruction, u8),
    IndirectX1(Instruction, u8),
    IndirectX2(Instruction, u8, u8),
    IndirectY0(Instruction, u8),
    IndirectY1(Instruction, u8, u8),
    ReadOrWrite(Instruction, u16),
    ReadInstruction(ReadInstruction, u8),
    ReadWriteInstruction(ReadWriteInstruction, u16, u8),
    WriteBack(u16, u8),
    ImpliedInstruction(ImpliedInstruction),
    PushInstruction(PushInstruction),
    PullInstruction0(PullInstruction),
    PullInstruction1(PullInstruction),
    BranchInstruction0(BranchInstruction, u8),
    BranchInstruction1(bool),
    JmpIndirect0(u16),
    JmpIndirect1(u16),
    Brk0,
    Brk1,
    Brk2,
    Brk3,
    Brk4,
    Rti0,
    Rti1,
    Rti2,
    Rti3,
    Rts0,
    Rts1,
    Rts2,
    Rts3,
    Jsr0(u8),
    Jsr1(u8),
    Jsr2(u8),
    Jsr3(u8),
}

#[derive(Debug)]
pub struct Cpu {
    a: u8,
    x: u8,
    y: u8,
    pc: u16,
    s: u8,
    p: Flags,
    mem: [u8; 0x10000],
    state: CpuState,
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
            mem: [0; 0x10000],
            state: CpuState::FetchOpCode,
        }
    }

    pub fn tick(&mut self) {
        self.state = match self.state {
            CpuState::FetchOpCode => self.fetch_opcode(),
            CpuState::FetchValue(opcode) => {
                let value = self.read_mem(self.pc);

                match (opcode.addressing_mode, opcode.instruction) {
                    (AddressingMode::Accumulator, _) | (AddressingMode::Implied, _) => {}
                    _ => self.increment_pc(),
                }

                match (opcode.addressing_mode, opcode.instruction) {
                    (AddressingMode::Accumulator, Instruction::ReadWrite(instruction)) => {
                        CpuState::Accumulator(instruction)
                    }
                    (AddressingMode::Accumulator, _) => unreachable!(),
                    (AddressingMode::IndirectX, _) => {
                        CpuState::IndirectX0(opcode.instruction, value)
                    }
                    (AddressingMode::ZeroPage, _) => {
                        CpuState::ReadOrWrite(opcode.instruction, value as u16)
                    }
                    (AddressingMode::Immediate, Instruction::Read(instruction)) => {
                        CpuState::ReadInstruction(instruction, value)
                    }
                    (AddressingMode::Immediate, _) => unreachable!(),
                    (AddressingMode::Absolute, Instruction::Jsr) => CpuState::Jsr0(value),
                    (AddressingMode::Absolute, _) => {
                        CpuState::Absolute(opcode.instruction, value, None)
                    }
                    (AddressingMode::IndirectY, _) => {
                        CpuState::IndirectY0(opcode.instruction, value)
                    }
                    (AddressingMode::ZeroPageX, _) => {
                        CpuState::ZeroPageIndexed(opcode.instruction, value, self.x)
                    }
                    (AddressingMode::ZeroPageY, _) => {
                        CpuState::ZeroPageIndexed(opcode.instruction, value, self.y)
                    }
                    (AddressingMode::AbsoluteY, _) => {
                        CpuState::Absolute(opcode.instruction, value, Some(self.y))
                    }
                    (AddressingMode::AbsoluteX, _) => {
                        CpuState::Absolute(opcode.instruction, value, Some(self.x))
                    }
                    (AddressingMode::Implied, Instruction::Implied(instruction)) => {
                        CpuState::ImpliedInstruction(instruction)
                    }
                    (AddressingMode::Implied, Instruction::Push(instruction)) => {
                        CpuState::PushInstruction(instruction)
                    }
                    (AddressingMode::Implied, Instruction::Pull(instruction)) => {
                        CpuState::PullInstruction0(instruction)
                    }
                    (AddressingMode::Implied, Instruction::Brk) => CpuState::Brk0,
                    (AddressingMode::Implied, Instruction::Rti) => CpuState::Rti0,
                    (AddressingMode::Implied, Instruction::Rts) => CpuState::Rts0,
                    (AddressingMode::Implied, _) => unreachable!(),
                    (AddressingMode::Relative, Instruction::Branch(instruction)) => {
                        CpuState::BranchInstruction0(instruction, value)
                    }
                    (AddressingMode::Relative, _) => unreachable!(),
                }
            }
            CpuState::Absolute(instruction, address_l, index) => {
                let address_h = self.read_mem(self.pc);

                match (index, instruction) {
                    (Some(register), instruction) => {
                        self.increment_pc();
                        let (address_l, pagebound_crossed) = address_l.overflowing_add(register);
                        let address = address(address_h, address_l);
                        if pagebound_crossed {
                            CpuState::PageCrossing(instruction, address)
                        } else {
                            CpuState::ReadOrWrite(instruction, address)
                        }
                    }
                    (None, Instruction::Jmp) => {
                        self.pc = address(address_h, address_l);
                        CpuState::FetchOpCode
                    }
                    (None, Instruction::JmpIndirect) => {
                        self.increment_pc();
                        CpuState::JmpIndirect0(address(address_h, address_l))
                    }
                    (None, _) => {
                        self.increment_pc();
                        CpuState::ReadOrWrite(instruction, address(address_h, address_l))
                    }
                }
            }
            CpuState::PageCrossing(instruction, address) => {
                let address_h = (address >> 8) as u8;
                let address = (address_h.wrapping_add(1) as u16) << 8 | (address & 0x00FF);
                CpuState::ReadOrWrite(instruction, address)
            }
            CpuState::Accumulator(instruction) => {
                self.a = self.execute_read_write_instruction(instruction, self.a);
                self.fetch_opcode()
            }
            CpuState::ZeroPageIndexed(instruction, address, register) => {
                let address = address.wrapping_add(register);
                CpuState::ReadOrWrite(instruction, address as u16)
            }
            CpuState::IndirectX0(instruction, pointer) => {
                let pointer = pointer.wrapping_add(self.x);
                CpuState::IndirectX1(instruction, pointer)
            }
            CpuState::IndirectX1(instruction, pointer) => {
                let address_l = self.read_mem(pointer as u16);
                let pointer = pointer.wrapping_add(1);
                CpuState::IndirectX2(instruction, pointer, address_l)
            }
            CpuState::IndirectX2(instruction, pointer, address_l) => {
                let address_h = self.read_mem(pointer as u16);
                CpuState::ReadOrWrite(instruction, address(address_h, address_l))
            }
            CpuState::IndirectY0(instruction, pointer) => {
                let address_l = self.read_mem(pointer as u16);
                let pointer = pointer.wrapping_add(1);
                CpuState::IndirectY1(instruction, pointer, address_l)
            }
            CpuState::IndirectY1(instruction, pointer, address_l) => {
                let address_h = self.read_mem(pointer as u16);
                let (address_l, pagebound_crossed) = address_l.overflowing_add(self.y);
                let address = address(address_h, address_l);
                if pagebound_crossed {
                    CpuState::PageCrossing(instruction, address)
                } else {
                    CpuState::ReadOrWrite(instruction, address)
                }
            }
            CpuState::ReadOrWrite(instruction, address) => match instruction {
                Instruction::Read(instruction) => {
                    let value = self.read_mem(address);
                    CpuState::ReadInstruction(instruction, value)
                }
                Instruction::ReadWrite(instruction) => {
                    let value = self.read_mem(address);
                    CpuState::ReadWriteInstruction(instruction, address, value)
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
                _ => unreachable!(),
            },
            CpuState::ReadInstruction(instruction, value) => {
                self.execute_read_instruction(instruction, value);
                self.fetch_opcode()
            }
            CpuState::ReadWriteInstruction(instruction, address, value) => {
                // in theory, at this point, a value is written to address
                // right before executing the instruction
                let value = self.execute_read_write_instruction(instruction, value);
                CpuState::WriteBack(address, value)
            }
            CpuState::WriteBack(address, value) => {
                self.write_mem(address, value);
                CpuState::FetchOpCode
            }
            CpuState::ImpliedInstruction(instruction) => {
                self.execute_implied_instruction(instruction);
                self.fetch_opcode()
            }
            CpuState::PushInstruction(instruction) => {
                self.execute_push_instruction(instruction);
                CpuState::FetchOpCode
            }
            CpuState::PullInstruction0(instruction) => {
                self.increment_s();
                CpuState::PullInstruction1(instruction)
            }
            CpuState::PullInstruction1(instruction) => {
                self.execute_pull_instruction(instruction);
                CpuState::FetchOpCode
            }
            CpuState::BranchInstruction0(instruction, value) => {
                if self.execute_branch_instruction(instruction) {
                    let pc_l = self.pc as u8;
                    let offset = value as i8;
                    let offset_positive = offset.is_positive();
                    let (pc_l, pagebound_crossed) = if offset_positive {
                        pc_l.overflowing_add(value)
                    } else {
                        pc_l.overflowing_sub(offset.unsigned_abs())
                    };
                    self.pc = (self.pc & 0xFF00) | pc_l as u16;
                    if pagebound_crossed {
                        CpuState::BranchInstruction1(offset_positive)
                    } else {
                        CpuState::FetchOpCode
                    }
                } else {
                    self.fetch_opcode()
                }
            }
            CpuState::BranchInstruction1(positive) => {
                let mut pc_h = (self.pc >> 8) as u8;
                pc_h = if positive {
                    pc_h.wrapping_add(1)
                } else {
                    pc_h.wrapping_sub(1)
                };
                self.pc = (pc_h as u16) << 8 | (self.pc & 0xFF);
                CpuState::FetchOpCode
            }
            CpuState::JmpIndirect0(address) => {
                self.pc = self.read_mem(address) as u16;
                CpuState::JmpIndirect1(address) // 6502 bug: page cross is not handled for this instruction
            }
            CpuState::JmpIndirect1(address) => {
                self.pc |= (self.read_mem(address.wrapping_add(1)) as u16) << 8;
                CpuState::FetchOpCode
            }
            CpuState::Brk0 => {
                self.stack_push((self.pc >> 8) as u8);
                CpuState::Brk1
            }
            CpuState::Brk1 => {
                self.stack_push(self.pc as u8);
                CpuState::Brk2
            }
            CpuState::Brk2 => {
                self.stack_push(self.p.bits());
                CpuState::Brk3
            }
            CpuState::Brk3 => {
                self.pc = self.read_mem(INTERRUPT_VECTOR) as u16;
                CpuState::Brk4
            }
            CpuState::Brk4 => {
                self.pc |= (self.read_mem(INTERRUPT_VECTOR + 1) as u16) << 8;
                CpuState::FetchOpCode
            }
            CpuState::Rti0 => {
                self.increment_s();
                CpuState::Rti1
            }
            CpuState::Rti1 => {
                self.p = Flags::from_bits_truncate(self.stack_pull());
                self.increment_s();
                CpuState::Rti2
            }
            CpuState::Rti2 => {
                self.pc = self.stack_pull() as u16;
                self.increment_s();
                CpuState::Rti3
            }
            CpuState::Rti3 => {
                self.pc |= (self.stack_pull() as u16) << 8;
                CpuState::FetchOpCode
            }
            CpuState::Rts0 => {
                self.increment_s();
                CpuState::Rts1
            }
            CpuState::Rts1 => {
                self.pc = self.stack_pull() as u16;
                self.increment_s();
                CpuState::Rts2
            }
            CpuState::Rts2 => {
                self.pc |= (self.stack_pull() as u16) << 8;
                CpuState::Rts3
            }
            CpuState::Rts3 => {
                self.increment_pc();
                CpuState::FetchOpCode
            }
            CpuState::Jsr0(address_l) => {
                // some internal operation
                CpuState::Jsr1(address_l)
            }
            CpuState::Jsr1(address_l) => {
                self.stack_push((self.pc >> 8) as u8);
                CpuState::Jsr2(address_l)
            }
            CpuState::Jsr2(address_l) => {
                self.stack_push(self.pc as u8);
                CpuState::Jsr3(address_l)
            }
            CpuState::Jsr3(address_l) => {
                let address_h = self.read_mem(self.pc);
                self.pc = address(address_h, address_l);
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

    fn fetch_opcode(&mut self) -> CpuState {
        let opcode = OpCode::from(self.read_mem(self.pc));
        self.increment_pc();
        CpuState::FetchValue(opcode)
    }

    fn increment_pc(&mut self) {
        // FIXME: not sure about this
        self.pc = self.pc.wrapping_add(1);
    }

    fn increment_s(&mut self) {
        self.s = self.s.wrapping_add(1);
    }

    fn set_zero_and_negative_flags(&mut self, value: u8) {
        self.p.set(Flags::Z, value == 0);
        self.p.set(Flags::N, value & 0x80 != 0);
    }

    fn execute_branch_instruction(&mut self, instruction: BranchInstruction) -> bool {
        match instruction {
            BranchInstruction::Bcc => self.bcc(),
            BranchInstruction::Bcs => self.bcs(),
            BranchInstruction::Beq => self.beq(),
            BranchInstruction::Bmi => self.bmi(),
            BranchInstruction::Bne => self.bne(),
            BranchInstruction::Bpl => self.bpl(),
            BranchInstruction::Bvc => self.bvc(),
            BranchInstruction::Bvs => self.bvs(),
        }
    }

    fn execute_implied_instruction(&mut self, instruction: ImpliedInstruction) {
        match instruction {
            ImpliedInstruction::Clc => self.clc(),
            ImpliedInstruction::Cld => self.cld(),
            ImpliedInstruction::Cli => self.cli(),
            ImpliedInstruction::Clv => self.clv(),
            ImpliedInstruction::Dex => self.dex(),
            ImpliedInstruction::Dey => self.dey(),
            ImpliedInstruction::Iny => self.iny(),
            ImpliedInstruction::Inx => self.inx(),
            ImpliedInstruction::Nop => {}
            ImpliedInstruction::Sec => self.sec(),
            ImpliedInstruction::Sed => self.sed(),
            ImpliedInstruction::Sei => self.sei(),
            ImpliedInstruction::Tax => self.tax(),
            ImpliedInstruction::Tay => self.tay(),
            ImpliedInstruction::Tsx => self.tsx(),
            ImpliedInstruction::Txa => self.txa(),
            ImpliedInstruction::Txs => self.txs(),
            ImpliedInstruction::Tya => self.tya(),
        }
    }

    fn execute_push_instruction(&mut self, instruction: PushInstruction) {
        match instruction {
            PushInstruction::Pha => self.pha(),
            PushInstruction::Php => self.php(),
        }
    }

    fn execute_pull_instruction(&mut self, instruction: PullInstruction) {
        match instruction {
            opcodes::PullInstruction::Pla => self.pla(),
            opcodes::PullInstruction::Plp => self.plp(),
        }
    }

    fn execute_read_instruction(&mut self, instruction: ReadInstruction, value: u8) {
        match instruction {
            ReadInstruction::Adc => self.adc(value),
            ReadInstruction::And => self.and(value),
            ReadInstruction::Bit => self.bit(value),
            ReadInstruction::Cmp => self.cmp(value),
            ReadInstruction::Eor => self.eor(value),
            ReadInstruction::Lda => self.lda(value),
            ReadInstruction::Ldx => self.ldx(value),
            ReadInstruction::Ldy => self.ldy(value),
            ReadInstruction::Ora => self.ora(value),
            ReadInstruction::Sbc => self.sbc(value),
            ReadInstruction::Cpx => self.cpx(value),
            ReadInstruction::Cpy => self.cpy(value),
        };
    }

    fn execute_read_write_instruction(
        &mut self,
        instruction: ReadWriteInstruction,
        value: u8,
    ) -> u8 {
        match instruction {
            ReadWriteInstruction::Asl => self.asl(value),
            ReadWriteInstruction::Dec => self.dec(value),
            ReadWriteInstruction::Inc => self.inc(value),
            ReadWriteInstruction::Lsr => self.lsr(value),
            ReadWriteInstruction::Rol => self.rol(value),
            ReadWriteInstruction::Ror => self.ror(value),
        }
    }

    fn adc(&mut self, value: u8) {
        let a = self.a as u16;
        let m = value as u16 + self.p.contains(Flags::C) as u16;
        let value = a + m;
        self.p
            .set(Flags::V, (a ^ value) & (m ^ value) & 0x0080 != 0);
        self.p.set(Flags::C, value & 0x0100 != 0);
        set_reg!(self, a, value as u8);
    }

    fn and(&mut self, value: u8) {
        set_reg!(self, a, self.a & value);
    }

    fn asl(&mut self, mut value: u8) -> u8 {
        let carry = value & 0x80;
        value <<= 1;
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

    fn bit(&mut self, value: u8) {
        let value = self.a & value;
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

    fn cmp(&mut self, value: u8) {
        let (value, overflow) = self.a.overflowing_sub(value);
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, !overflow);
    }

    fn cpx(&mut self, value: u8) {
        let (value, overflow) = self.x.overflowing_sub(value);
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, !overflow);
    }

    fn cpy(&mut self, value: u8) {
        let (value, overflow) = self.y.overflowing_sub(value);
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

    fn eor(&mut self, value: u8) {
        set_reg!(self, a, self.a ^ value);
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

    fn lda(&mut self, value: u8) {
        set_reg!(self, a, value);
    }

    fn ldx(&mut self, value: u8) {
        set_reg!(self, x, value);
    }

    fn ldy(&mut self, value: u8) {
        set_reg!(self, y, value);
    }

    fn lsr(&mut self, mut value: u8) -> u8 {
        let carry = value & 0x01;
        value >>= 1;
        self.set_zero_and_negative_flags(value);
        self.p.set(Flags::C, carry != 0);
        value
    }

    fn ora(&mut self, value: u8) {
        set_reg!(self, a, self.a | value);
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

    fn sbc(&mut self, value: u8) {
        let a = self.a as u16;
        let m = value as u16 + 1 - (self.p.contains(Flags::C) as u16);
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

fn address(address_h: u8, address_l: u8) -> u16 {
    (address_h as u16) << 8 | address_l as u16
}
