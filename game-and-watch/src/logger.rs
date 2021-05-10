use panic_semihosting as _;

use lazy_static::lazy_static;
use log::LevelFilter;

pub use cortex_m_log::log::Logger;
use cortex_m_log::printer::semihosting;
use cortex_m_log::printer::semihosting::Semihosting;
use cortex_m_log::modes::InterruptOk;
use cortex_m_semihosting::hio::HStdout;

lazy_static! {
    static ref LOGGER: Logger<Semihosting<InterruptOk, HStdout>> = Logger {
        level: LevelFilter::Info,
        inner: semihosting::InterruptOk::<_>::stdout().expect("Get Semihosting stdout"),
    };
}

pub fn init() {
    cortex_m_log::log::init(&LOGGER).unwrap();
}