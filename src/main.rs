//! modular arithmetic generator

#![crate_type = "bin"]
#![crate_name = "modp"]

#![feature(slicing_syntax, quote, globs)]

extern crate num;
extern crate syntax;

use num::bigint::{BigUint, ToBigUint};
use syntax::print::{pp, pprust};

pub mod util;
pub mod gapless;

fn main() {
    let n130 = 1u8.to_biguint().unwrap() << 130;
    let five = 5u8.to_biguint().unwrap();
    let p1305: BigUint = &n130 - &five;
    let code = gapless::generate("Int1305", &p1305, 32);

    let stdout = box std::io::stdout() as Box<Writer + 'static>;
    let mut ps = pprust::rust_printer(stdout);
    ps.print_mod(&code, &[]).unwrap();
    ps.print_remaining_comments().unwrap();
    pp::eof(&mut ps.s).unwrap();
    ps.s.out.flush().unwrap();
}
