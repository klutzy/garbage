use std::iter::AdditiveIterator;
use num::bigint::{BigUint, ToBigUint};
use syntax::ast;
use syntax::codemap::{DUMMY_SP, dummy_spanned};
use syntax::parse;
use syntax::parse::token;
use syntax::ptr::P;

use util::*;

// TODO use signed for more fun

fn limb_bit_size(r: &[u8]) -> u8 {
    let bit_max = *r.iter().max().unwrap();
    match bit_max {
        1...8 => 8,
        9...16 => 16,
        17...32 => 32,
        33...64 => 64,
        _ => panic!("unsupported limb size: {:?}", r),
    }
}

/// `struct $name([T; N])` represents
/// `t[0] + t[1] * 2^r[0] + t[2] * 2^(r[0] + r[1]) + ...`.
///
/// n, m represents prime `2^n - m`.
/// r: bit size of each limb. each limb must have size `> 8`.
pub fn generate(name: &str, n: u32, m: u32, r: &[u8]) -> ast::Mod {
    let sess = parse::new_parse_sess();
    let qcx = QuoteCtxt::new("p", &sess);
    let mut items = Vec::new();

    let pown = 1u8.to_biguint().unwrap() << (n as usize);
    let p = pown - m.to_biguint().unwrap();

    let limb_bit_size = limb_bit_size(r);
    let p_vec = biguint_to_vec(&p, limb_bit_size);

    let total_bytes = (r.iter().map(|&x| x).sum() + 7) / 8;

    let len = r.len();
    let limb_bytes = (limb_bit_size / 8) * 8;
    let limb_extra_bits = limb_bytes * 8 - limb_bit_size;

    let ty = size_to_ty(limb_bit_size);
    let ty2 = size_to_ty(limb_bit_size * 2);

    let name = token::str_to_ident(name);
    let struct_item = quote_item!(&qcx.cx,
        // TODO: remove `pub` after debugging
        pub struct $name(pub [$ty; $len]);
    ).expect("quote_item error");
    items.push(struct_item);

    // TODO
    // let prime = token::str_to_ident("P");
    // let prime_item = quote_item!(&qcx.cx,
    //     pub static $prime: $name = $name($prime_array);
    // ).expect("quote_item failed to create prime item");
    // items.push(prime_item);

    let (from_bytes_method, to_bytes_method) = {
        let mut from_stmts = Vec::new();
        let mut to_stmts = Vec::new();

        let v = token::str_to_ident("v");
        let b = token::str_to_ident("b");

        // `$b[$bi]`, `$b_bit_offset`-th bit.
        let mut bi = 0us;
        // XXX: usize only for easy quote. it can be fixed if shift permits u8
        let mut b_bit_offset = 0us;
        for (i, &ri) in r.iter().enumerate() {
            // XXX: same here.
            let ri = ri as usize;

            let mut v_offset = 0us;

            if b_bit_offset > 0 {
                // we used only partial portion of `$b[$bi]`. use the remaining bits here.
                let from_stmt = quote_stmt!(&qcx.cx,
                    $v[$i] |= ($b[$bi] as $ty) >> $b_bit_offset;
                );
                from_stmts.push(from_stmt);

                let to_stmt = quote_stmt!(&qcx.cx,
                    $b[$bi] |= (self.0[$i] << $b_bit_offset) as u8;
                );
                to_stmts.push(to_stmt);

                v_offset += 8 - b_bit_offset;
                b_bit_offset = 0;
                bi += 1;
            }

            while v_offset + 8 <= ri {
                let from_stmt = quote_stmt!(&qcx.cx,
                    $v[$i] |= ($b[$bi] as $ty) << $v_offset;
                );
                from_stmts.push(from_stmt);

                let to_stmt = quote_stmt!(&qcx.cx,
                    $b[$bi] |= (self.0[$i] >> $v_offset) as u8;
                );
                to_stmts.push(to_stmt);

                v_offset += 8;
                bi += 1;
            }

            b_bit_offset = ri - v_offset;
            if b_bit_offset > 0 {
                let from_stmt = quote_stmt!(&qcx.cx,
                    $v[$i] |= (($b[$bi] as $ty) & ((1 << $b_bit_offset) - 1) ) << $v_offset;
                );
                from_stmts.push(from_stmt);

                let to_stmt = quote_stmt!(&qcx.cx,
                    $b[$bi] |= (self.0[$i] >> $v_offset) as u8 & ((1 << $b_bit_offset) - 1);
                );
                to_stmts.push(to_stmt);
            }
        }

        let from_bytes = quote_method!(&qcx.cx,
            pub fn from_bytes_le($b: &[u8]) -> Option<$name> {
                if $b.len() != $total_bytes {
                    return None;
                }
                let mut $v = [0; $len];

                $from_stmts

                Some($v)
            }
        );

        let to_bytes = quote_method!(&qcx.cx,
            pub fn to_bytes_le(&self) -> Vec<u8> {
                let mut $b = [0; $total_bytes];

                $to_stmts

                $b.to_vec()
            }
        );

        (from_bytes, to_bytes)
    };

    let impl_item = quote_item!(&qcx.cx,
        impl $name {
            $from_bytes_method
            $to_bytes_method

            pub fn add(&self, b: &$name) -> $name {
                let mut v = $name([0, ..$len]);

                for i in (0u..$len) {
                    v.0[i] = self.0[i] + b.0[i];
                }

                v
            }

            pub fn double(&self) -> $name {
                let mut v = $name([0, ..$len]);

                for i in (0u..$len) {
                    v.0[i] = self.0[i] << 1;
                }

                v
            }
        }
    ).expect("quote_item failed for impl");
    items.push(impl_item);

    ast::Mod {
        inner: DUMMY_SP,
        view_items: Vec::new(),
        items: items,
    }
}
