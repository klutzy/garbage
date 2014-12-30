#![feature(slicing_syntax)]

extern crate num;

use std::rand::{Rng, SeedableRng, IsaacRng};
use num::bigint::{BigUint, ToBigUint, BigDigit};

// TODO tests are hardcoded for mod (2^130 - 5)

use gen::{Int1305, P};

#[allow(missing_copy_implementations)]
pub mod gen;

#[cfg(not(test))]
fn main() {}

fn p() -> BigUint {
    let p = P.to_bytes_le();
    let p = bytes_to_biguint(&*p);
    p
}

// little-endian
// NOTE: not normalized!
fn bytes_to_biguint(b: &[u8]) -> BigUint {
    let zero: BigUint = 0u8.to_biguint().unwrap();
    let mut val = zero;
    for i in b.iter().rev() {
        val = val << 8;
        val = &val + &(*i).to_biguint().unwrap();
    }

    val
}

pub fn biguint_to_bytes(u: &BigUint) -> Vec<u8> {
    use std::num::Int;

    // since div_mod_floor is super slow...
    let v: &Vec<BigDigit> = unsafe { std::mem::transmute(u) };

    let len = 17u; // 2^130-5 hardcode

    let mut ret = Vec::new();
    for i in v.iter() {
        // assumes BigDigit is u32
        let t: [u8; 4] = unsafe { std::mem::transmute(i.to_le()) };
        ret.push_all(&t);
    }

    for _ in (ret.len()..len) {
        ret.push(0);
    }

    ret = ret[..len].to_vec();

    ret
}

fn tests() -> Vec<BigUint> {
    let seed: &[u32] = &[1u32, 2, 3];
    let mut rng: IsaacRng = SeedableRng::from_seed(seed);
    let mut ret: Vec<BigUint> = Vec::new();

    // easy special values
    ret.push(0u8.to_biguint().unwrap());
    let one = 1u8.to_biguint().unwrap();
    ret.push(one.clone());
    ret.push(2u8.to_biguint().unwrap());

    let e10 = 1u8.to_biguint().unwrap() << 10;
    let e26 = 1u8.to_biguint().unwrap() << 26;
    let e50 = 1u8.to_biguint().unwrap() << 50;
    ret.push(e10.clone());
    ret.push(e26.clone());
    ret.push(e50.clone());
    ret.push(one + e50);

    let mut buf = [0u8; 17];
    let p = p();
    for _ in 0u..100 {
        rng.fill_bytes(&mut buf);
        let new_num = bytes_to_biguint(&buf) % p.clone();
        ret.push(new_num);
    }

    ret
}

#[test]
fn test_test_from_bytes() {
    let tests = tests();
    for a in tests.iter() {
        let a_b = biguint_to_bytes(a);
        let a_u = bytes_to_biguint(&*a_b);
        assert_eq!(*a, a_u);
    }
}

#[test]
fn test_from_to_bytes() {
    let tests = tests();
    for a in tests.iter() {
        let a_b = biguint_to_bytes(a);

        println!("a_b: {}", a_b);
        let a_i = Int1305::from_bytes_le(&*a_b).expect("from_bytes failed1");
        let a_i_b = a_i.to_bytes_le();

        assert_eq!(a_b, a_i_b);
    }
}

#[test]
fn test_arith() {
    let p = p();
    let tests = tests();

    fn check(expected: BigUint, actual: Int1305) {
        let expected_b = biguint_to_bytes(&expected);

        let actual_b = actual.to_bytes_le();

        if expected_b != actual_b {
            panic!("expected {} ({}), found {}", expected_b, expected, actual_b);
        }
    }

    for a in tests.iter() {
        let a_b = biguint_to_bytes(a);
        let a_i = Int1305::from_bytes_le(&*a_b).expect("from_bytes failed2");
        for b in tests.iter() {
            let b_b = biguint_to_bytes(b);
            let b_i = Int1305::from_bytes_le(&*b_b).expect("from_bytes3 failed");

            let expected: BigUint = (a + b) % p.clone();
            let actual = a_i.add(&b_i);
            check(expected, actual);

            let expected: BigUint = (a + p.clone() - b) % p.clone();
            let actual = a_i.sub(&b_i);
            check(expected, actual);

            let expected: BigUint = (a * b) % p.clone();
            let actual = a_i.mult(&b_i);

            check(expected, actual);
        }
    }
}
