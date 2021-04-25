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
    cpu.tick(); // fetch address high byte and add y to the low address byte, page bound crossing detected
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
    cpu.tick(); // fetch address high byte and add x to the low address byte, page bound crossing detected
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
    cpu.tick(); // fetch address high byte and add x to the low address byte, page bound crossing detected
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
fn bcc() {
    // these instructions are set at RAM_CODE_START
    let instructions = [
        0x90, 0x02, // BCC $02
        0x29, 0x55, // AND #$55
        0x29, 0xaa, // AND #$aa
        0x90, 0xfa, // BCC $fa // -6
        0x09, 0xff, // OR #$ff
    ];
    let mut cpu = setup(&instructions);

    // condition is false
    cpu.a = 0xff;
    cpu.p.set(Flags::C, true);
    cpu.tick(); // fetch opcode
    cpu.tick(); // fetch offset
    cpu.tick(); // condition is false, fetch next opcode
    cpu.tick(); // fetch immediate value
    cpu.tick(); // fetch next opcode and execute
    assert_eq!(cpu.a, 0x55);

    // condition is true, forward jump to AND #$aa, no page bound crossed
    cpu.reset();
    cpu.a = 0xff;
    cpu.tick(); // fetch opcode
    cpu.tick(); // fetch offset
    cpu.tick(); // condition is true, set PC
    cpu.tick(); // fetch opcode
    cpu.tick(); // fetch immediate value
    assert_eq!(cpu.a, 0xff);
    cpu.tick(); // fetch next opcode and execute
    assert_eq!(cpu.a, 0xaa);

    // condition is still true, backward jump to AND #$55, no page bound crossed
    cpu.tick(); // fetch offset
    cpu.tick(); // condition is true, set PC
    cpu.tick(); // fetch opcode
    cpu.tick(); // fetch immediate value
    assert_eq!(cpu.a, 0xaa);
    cpu.tick(); // fetch next opcode and execute
    assert_eq!(cpu.a, 0x00);

    // condition is true, forward jump to AND #$aa, page bound crossed
    cpu.reset();
    cpu.a = 0xff;
    let instructions_offset = 0xfc;
    cpu.pc = RAM_CODE_START + instructions_offset;
    instructions.iter().enumerate().for_each(|(index, &value)| {
        cpu.write_mem(RAM_CODE_START + instructions_offset + index as u16, value);
    });

    cpu.tick(); // fetch opcode
    cpu.tick(); // fetch offset
    cpu.tick(); // condition is true, set PC, pagebound crossing detected
    cpu.tick(); // fix PCH
    cpu.tick(); // fetch opcode
    cpu.tick(); // fetch immediate value
    assert_eq!(cpu.a, 0xff);
    cpu.tick(); // fetch next opcode and execute
    assert_eq!(cpu.a, 0xaa);

    // condition is still true, backward jump to AND #$55, page bound crossed
    cpu.tick(); // fetch offset
    cpu.tick(); // condition is true, set PC, pagebound crossing detected
    cpu.tick(); // fix PCH
    cpu.tick(); // fetch opcode
    cpu.tick(); // fetch immediate value
    assert_eq!(cpu.a, 0xaa);
    cpu.tick(); // fetch next opcode and execute
    assert_eq!(cpu.a, 0x00);
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
