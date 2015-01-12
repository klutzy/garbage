use std::iter::AdditiveIterator;
use num::bigint::{BigUint, ToBigUint};
use syntax::ast;
use syntax::codemap::{DUMMY_SP, dummy_spanned};
use syntax::parse;
use syntax::parse::token;
use syntax::ptr::P;

use util::*;

// TODO use signed for more fun

fn sum(a: &[u8]) -> usize {
    a.iter().map(|x| (*x as u16)).sum() as usize
}

// with non-uniform limb, multiplication becomes more interesting!
// suppose we have x = x0 + r0 * (x1 + r1 * ...) and y as well.
// x * y = (x0 * y0)
//         + r1 * x1 * y0 + r1 * x0 * y1
//         + r1 * r2 * x2 * y0 + r1 * r1 * x1 * y1 + r1 * r2 * x0 * y2
//         + ...
// note that r1 * r1 may be different r1 * r2 and so on.
// suppose r1 * r1 >= r1 * r2 and so on.
// define d[k,i] = (r0 * ... * r[i-1]) * (r0 * ... * r[k-i-1]) / r0 * ... * r[k-1].
// it must be natural numbers!
// (bydef d[k,i] = d[k,k-i] and d[k,0] = 1)
// x * y = (x0 * y0)
//         + r1 * (x1 * y0 + x0 * y1)
//         + (r1 * r2) * (x2 * y0 + d21 * x1 * y1 + x0 * y2)
//         + (r1 * r2 * r3) * (x3 * y0 + d31 * (x2 * y1 + x1 * y2) + x0 * y3)
//         + (r1 * ... * r4) * (x4 * y0 + d41 * (x3 * y1 + x1 * y3) + d42 * (x2 * y2) + x0 * y4)
//         + ...
//
// (here we also assume `r` is repeated after r[len-1].
// also, (x * y)[k] requires k additions of x[i] * y[k-i] * d[i,k],
// so roughly ty2.bits >= max(x[_].bits) + max(y[_].bits) + max(d[_].bits) + lg(k)
// (also, since we use lazy normalization on addition, x[_].bits here is slightly
// larger than r[i].)
fn limb_mult_shift(r2: &[u8], k: usize, i: usize) -> usize {
    let rk = sum(&r2[..k]);
    let ri = sum(&r2[..i]);
    let rki = sum(&r2[..(k - i)]);
    if rk > ri + rki {
        panic!("limbs have pathological length: i {}, k {}", i, k);
    }
    println!("// k {} i {} ri {} rki {} rk {} r2 {:?}", k, i, ri, rki, rk, r2);
    ri + rki - rk
}

fn expand_limbs(n: u32, r: &[u8]) -> Vec<u8> {
    let r_bits = sum(r);
    let n = n as usize;
    if n % r_bits != 0 {
        panic!("prime bits ({}) % size of base limbs ({}) != 0", n, r_bits);
    }

    let num = n / r_bits;
    let mut ret = Vec::new();
    for _ in (0..num) {
        ret.push_all(r);
    }
    ret
}

// `struct $name([T; N])` represents
// `t[0] + t[1] * 2^r[0] + t[2] * 2^(r[0] + r[1]) + ...`.
//
// n, m represents prime `2^n - m`.
// r: bit size of each limb. assumptions:
// sum(r) must be divisibly by n.
// r is implicitly repeated. [26, 25] means 26, 25, 26, 25, ...
// (e.g. 255 == (26 + 25) * 5. this is used for doublewidth reduction:
// if a * b == c0 + 2^255 * c1 then c0 and c1 has same limb representation.)
// for any i and k, `r[0] * ... * r[k-1] >= (r[0] * ... r[i-1]) * (r[0] * ... * r[k-i-1]).
// each limb must have size `> 8`.
// TODO check the assumptions
pub fn generate(name: &str, limb_bit_size: u8, n: u32, m: u32, r: &[u8]) -> ast::Mod {
    let sess = parse::new_parse_sess();
    let qcx = QuoteCtxt::new("p", &sess);
    let mut items = Vec::new();

    let p = (1u8.to_biguint().unwrap() << (n as usize)) - m.to_biguint().unwrap();

    let p_vec = biguint_to_vec(&p, limb_bit_size);

    let total_bytes = (n + 7) / 8;

    let r = expand_limbs(n, r);
    let len = r.len();
    let r2 = {
        let mut r2 = r.clone();
        r2.push_all(&*r);
        r2
    };
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

    let mult_method = {
        let mut stmts = Vec::new();

        // k == i + j
        for k in (0..(len * 2)) {
            for i in (0..len) {
                if i >= len || k < i || k - i >= len {
                    continue;
                }
                let j = k - i;
                let d = limb_mult_shift(&*r2, k, i);
                let stmt = quote_stmt!(&qcx.cx,
                    m[$k] += (self.0[$i] as $ty2) * (b.0[$j] as $ty2) << $d;
                );
                stmts.push(stmt);
            }
        }

        quote_method!(&qcx.cx,
            pub fn mult(&self, b: &$name) -> $name {
                let mut m = [0; $len * 2];

                $stmts
            }
        )
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

            pub fn normalize(&self) -> $name {
                // TODO
            }

            $mult_method
        }
    ).expect("quote_item failed for impl");
    items.push(impl_item);

    ast::Mod {
        inner: DUMMY_SP,
        view_items: Vec::new(),
        items: items,
    }
}
