#![no_main]
#![no_std]

mod logger;

use cortex_m;
use cortex_m_rt::entry;
use stm32h7xx_hal::{pac, prelude::*, hal::digital::v2::InputPin};

#[entry]
fn main() -> ! {
    logger::init();

    //let cp = cortex_m::Peripherals::take().unwrap();
    let dp = pac::Peripherals::take().unwrap();

    let pwr = dp.PWR.constrain();
    let pwrcfg = pwr.freeze();

    let rcc = dp.RCC.constrain();
    let ccdr = rcc.sys_ck(100.mhz()).freeze(pwrcfg, &dp.SYSCFG);

    let gpiod = dp.GPIOD.split(ccdr.peripheral.GPIOD);

    let button_a = gpiod.pd9.into_pull_up_input();

    loop {
        let result = button_a.is_high().unwrap();
        log::info!("{}", result);
        cortex_m::asm::delay(10000000);
    }

}
