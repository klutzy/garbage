// `[T; N]` represents `t[0] + t[1] * limb + t[2] * limb^2 + ...`
// this tries to be const-time, but llvm can do unfortunate optimizations.

use num::BigUint;
use syntax::ast;
use syntax::codemap::DUMMY_SP;
use syntax::parse;
use syntax::parse::token;

use util::*;

/// limb_size: bit size of each limb (u8, u16, u32)
pub fn generate(name: &str, p: &BigUint, limb_bit_size: u8) -> ast::Mod {
    let sess = parse::new_parse_sess();
    let qcx = QuoteCtxt::new("p", &sess);
    let mut items = Vec::new();

    // the number of bytes when serialized
    let total_bytes = (p.bits() + 7) / 8;
    // the number of limbs
    let len = limbs(p, limb_bit_size);

    let p_vec = biguint_to_vec(p, limb_bit_size);
    let barrett = barrett_constant(p, limb_bit_size, len);
    let barrett_vec = biguint_to_vec(&barrett, limb_bit_size);

    let ty = size_to_ty(limb_bit_size);
    let ty2 = size_to_ty(limb_bit_size * 2);

    // quote likes usize
    let len = len as usize;
    let limb_bit_size = limb_bit_size as usize;
    let limb_size = limb_bit_size as usize / 8;

    let prime_array = slice_to_expr(&*p_vec);
    let barrett_array = slice_to_expr(&*barrett_vec);
    let barrett_len = len + 1;

    let name = token::str_to_ident(name);
    let struct_item = quote_item!(&qcx.cx,
        pub struct $name([$ty; $len]);
    ).expect("quote_item error");
    items.push(struct_item);

    let prime = token::str_to_ident("P");
    let prime_item = quote_item!(&qcx.cx,
        pub static $prime: $name = $name($prime_array);
    ).expect("quote_item failed to create prime item");
    items.push(prime_item);

    let barrett = token::str_to_ident("B");
    let prime_item = quote_item!(&qcx.cx,
        pub static $barrett: [$ty; $barrett_len] = $barrett_array;
    ).expect("quote_item failed to create barrett item");
    items.push(prime_item);

    let impl_item = quote_item!(&qcx.cx,
        impl $name {
            // little endian
            pub fn from_bytes_le(v: &[u8]) -> Option<$name> {
                if v.len() != $total_bytes {
                    return None;
                }

                let mut ret: [$ty; $len] = [0; $len];
                for i in 0..$len {
                    for j in (0..$limb_size) {
                        let idx = i * $limb_size + j;
                        if idx >= $total_bytes {
                            break;
                        }
                        ret[i] |= (v[idx] as $ty) << (j * 8);
                    }
                }

                Some($name(ret))
            }

            pub fn to_bytes_le(&self) -> Vec<u8> {
                let mut b = [0u8; $total_bytes];
                for i in (0us..$len) {
                    for j in (0..$limb_size) {
                        let idx = i * $limb_size + j;
                        if idx >= $total_bytes {
                            break;
                        }
                        b[idx] = (self.0[i] >> (j * 8)) as u8;
                    }
                }

                b.to_vec()
            }

            // FIXME: this interface looks horrible; follow `const_if` signature
            // (i.e. swap a and b)
            // if flag == 0, returns a
            // if flag == 1, returns b
            pub fn choose(flag: $ty, a: &$name, b: &$name) -> $name {
                let mut v = [0; $len];
                // switch = if flag == 1 { 0 } else { 0b111...111 }
                let switch = flag - 1;
                for i in (0..$len) {
                    let axb = a.0[i] ^ b.0[i];
                    // mask = if flag == 1 { 0 } else { a ^ b }
                    let mask = axb & switch;
                    v[i] = b.0[i] ^ mask;
                }
                $name(v)
            }

            // return (value, carry) where
            // value = self + b mod 2^256
            // carry = if self + b < p { 0 } else { 1 }
            // i.e. self + b == value + 2^256 * carry
            // (carry is redundant if `p * 2 < limb^len`)
            fn add_no_reduce(&self, b: &$name) -> ($name, $ty) {
                let mut v = $name([0; $len]);

                // invariant: carry <= 1
                let mut carry: $ty2 = 0;
                for i in (0us..$len) {
                    // add <= 2^($limb_bit_size + 1)
                    let add = (self.0[i] as $ty2) + (b.0[i] as $ty2) + carry;
                    v.0[i] = add as $ty;
                    carry = add >> $limb_bit_size;
                }
                (v, carry as $ty)
            }

            // return (value, carry) where
            // value = self - b mod 2^256
            // carry = if self > b { 0 } else { 1 }
            // i.e. self - b == value - 2^256 * carry
            fn sub_no_reduce(&self, b: &$name) -> ($name, $ty) {
                let mut v = $name([0; $len]);

                // invariant: carry_sub <= 1
                let mut carry_sub: $ty2 = 0;
                for i in (0us..$len) {
                    // -2^$limb_bit_size <= sub <= 2^$limb_bit_size
                    let sub = (self.0[i] as $ty2) - (b.0[i] as $ty2) - carry_sub;
                    // if sub < 0, set carry_sub = 1 and sub += 2^$limb_bit_size
                    carry_sub = sub >> ($limb_bit_size * 2 - 1);
                    v.0[i] = sub as $ty;
                }

                (v, carry_sub as $ty)
            }

            // given `input = self + carry * limb^len` and `input < 2 * p`,
            // return `input` if `input < p` and `input - p` if `p <= input < 2 * p`.
            fn reduce_once(&self, carry: $ty) -> $name {
                let (v, carry_sub) = self.sub_no_reduce(&$prime);
                debug_assert!(!(carry_sub == 0 && carry == 1));
                let choose_new = carry ^ (carry_sub as $ty);
                $name::choose(choose_new, &v, self)
            }

            pub fn add(&self, b: &$name) -> $name {
                let (v, carry) = self.add_no_reduce(b);
                let v = v.reduce_once(carry);
                v
            }

            pub fn double(&self) -> $name {
                // FIXME: can be more efficient?
                self.add(self)
            }

            pub fn sub(&self, b: &$name) -> $name {
                let (v, carry_sub) = self.sub_no_reduce(b);
                let (v2, _carry_add) = v.add_no_reduce(&$prime);
                debug_assert!(!(_carry_add == 0 && carry_sub == 1));
                $name::choose(carry_sub as $ty, &v, &v2)
            }

            pub fn mult(&self, b: &$name) -> $name {
                // c must be zeros.
                fn mult_inner(a: &[$ty], b: &[$ty], c: &mut [$ty]) {
                    let alen = a.len();
                    let blen = b.len();
                    debug_assert_eq!(alen + blen, c.len());
                    for i in 0us..(alen) {
                        // invariant: carry <= 2^$limb_bit_size
                        let mut carry: $ty2 = 0;
                        for j in 0us..(blen) {
                            // c[i+j], carry <= 2^limb_bit_size - 1
                            // a[i] * b[j] <= (2^(limb_bit_size) - 1)^2
                            // therefore uv <= 2^(2 * limb_bit_size) - 1
                            let uv = (c[i + j] as $ty2) + (a[i] as $ty2) * (b[j] as $ty2) + carry;
                            c[i + j] = uv as $ty;
                            carry = uv >> $limb_bit_size;
                        }
                        c[i + blen] = carry as $ty;
                    }
                }

                let mut x: [$ty; $len * 2us] = [0; $len * 2us];
                mult_inner(&self.0, &b.0, &mut x);

                // # Barrett reduction
                //
                // we want to find q and r s.t. x == q * p + r and `0 <= r < k * p`
                // where `k` is not too large.
                //
                // (`q = x / p` yields `k = 1` but it's expensive.)
                //
                // instead, we use:
                // `q = ((x / limb^(len-1) * (limb^(len*2) / p)) / limb^(len+1)`
                // then `0 <= r < 3 * p`. here `a / limb^b` is easy and
                // `limb^(len*2) / p` is precomputed as `B`.
                // then we can compute `r = x - q * p` then reduce `r` 3 times.

                // q0 = (x / limb^(len-1)) * B
                let mut q0: [$ty; $len * 2us + 2us] = [0; $len * 2us + 2us];
                mult_inner(&x[($len - 1)..], &$barrett, &mut q0);
                let q = &q0[($len + 1)..]; // length $len + 1

                // FIXME: actually we only need `qp[..$len+1]`.
                let mut qp: [$ty; $len * 2us + 1us] = [0; $len * 2us + 1us];
                mult_inner(q, &$prime.0, &mut qp);

                // compute `x - qp`.
                // we already know that `0 <= r < 3 * p` so we don't have to
                // compute full subtraction.
                // instead, we compute `(x - qp) mod limb^k` where `k` satisfies
                // `3 * p < limb^k`.
                // we use `k = $len + 1`. (this is always true for `p > 3`)
                //
                // (if `3 * p < $len`, `r_carry` can be eliminated)
                let (r, r_carry) = {
                    let mut r = [0; $len];
                    let mut carry_sub: $ty2 = 0; // 1-bit
                    for i in 0..($len) {
                        let sub = (x[i] as $ty2) - (qp[i] as $ty2) - carry_sub;
                        carry_sub = sub >> ($limb_bit_size * 2 - 1);
                        r[i] = sub as $ty;
                    }

                    let sub = (x[$len] as $ty2) - (qp[$len] as $ty2) - carry_sub;
                    // `carry <= 3`
                    let carry = sub as $ty;

                    ($name(r), carry)
                };

                // now `r + carry * limb^len < p * 3`. subtrace `p` twice.
                let (r1, r1_carry) = {
                    // we can't use `reduce_once()` since it requires input to be `< 2 * p`.
                    let (r1, carry_sub) = r.sub_no_reduce(&$prime);
                    // carry_new can be 1, 0, or -1. the latter case implies `r < p`.
                    let carry_new = r_carry - carry_sub;

                    // choose_new = if carry_new < 0 { 1 } else { 0 }
                    let choose_new = carry_new >> ($limb_bit_size - 1);
                    let r1 = $name::choose(choose_new, &r1, &r);
                    // r1_carry = if carry_new < 0 { 0 } else { carry_new }
                    // (exploting the fact that carry_new is 1-bit)
                    let r1_carry = (carry_new & 1) ^ choose_new;

                    (r1, r1_carry)
                };

                let r2 = r1.reduce_once(r1_carry);
                r2
            }
        }
    ).expect("quote_item failed for impl");
    items.push(impl_item);

    ast::Mod {
        inner: DUMMY_SP,
        items: items,
    }
}
