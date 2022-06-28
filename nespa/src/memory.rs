pub trait Memory {
    fn read(&self, address: u16) -> u8;
    fn read_u16(&self, address: u16) -> u16;

    fn write(&mut self, address: u16, value: u8);
    fn write_u16(&mut self, address: u16, value: u16);
}
