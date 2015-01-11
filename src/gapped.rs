use num::bigint::{BigUint, ToBigUint};
use syntax::ast;
use syntax::codemap::{DUMMY_SP, dummy_spanned};
use syntax::parse;
use syntax::parse::token;
use syntax::ptr::P;

// TODO use signed for more fun

fn limb_bit_size(r: &[u8]) -> uint {
    (r.iter().max() as uint / 8) * 8
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

    let pown = 1u8.to_biguint().unwrap() << (n as uint);
    let p = pown - m.to_biguint().unwrap();

    let p_vec = biguint_to_vec(&p, limb_bit_size);

    let total_bytes = (r.iter().sum() + 7) / 8;

    let len = r.len();
    let limb_bit_size = limb_bit_size(r);
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

    let prime = token::str_to_ident("P");
    let prime_item = quote_item!(&qcx.cx,
        pub static $prime: $name = $name($prime_array);
    ).expect("quote_item failed to create prime item");
    items.push(prime_item);

    // suppose we have r = [3, 4, 5, 6].
    // total bits: 18
    // total bytes: 5
    // // b_offset = 0;
    // // b_index = 0;
    // // r_index = 0;
    // r0 = b[0] & (3 bits);
    // // 0, b_offset 3, 1
    // // 8 - 3 == 5 >= 4
    // r1 = (b[0] >> 3) & (4 bits);
    // // b_index 0, b_offset 7, r_index 2
    // // 8 - 7 == 1 />= 5
    // r2 = (b[0] >> 7)
    // // prev_offset = 1
    //      | () << 1;

    let from_bytes_method = {
        // op_info: (v_index, v_offset, rshift, bits, lshift)
        // at least one of rshift or lshift is 0 (because we assume each limb size > 8)
        let mut op_infos = Vec::new();

        let offset = 0; // bit offset
        let index = 0;
        for (i, &ri) in r.iter().enumerate() {
            let available = 8 - offset;
            let mut r_offset = 0;
            while ri >= available {
                // r[i] = r[i] | ((v[index] as u?? >> offset) & (ri bits)) << r_offset

                index += 1;
                r_offset += ri;
            }
        }

        let limbs = P(dummy_spanned(ast::ExprVec(limbs)));

        quote_item!(&qcx.cx,
            // little endian
            pub fn from_bytes_le(v: &[u8]) -> Option<$name> {
                if v.len() != $total_bytes {
                    return None;
                }

                Some($limbs)
            }
        )
    };

    let impl_item = quote_item!(&qcx.cx,
        impl $name {
            $from_bytes_method

            pub fn to_bytes_le(&self) -> Vec<u8> {
                // TODO
            }

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
