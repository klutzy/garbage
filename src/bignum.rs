// bignum implementation
// just for validation. do not use in production

use syntax::ast;
use syntax::codemap::{mod, DUMMY_SP};
use syntax::parse;
use syntax::parse::token;
use syntax::ptr::P;

use num::bigint::BigUint;

use util::*;

pub fn generate(name: &str, p: &BigUint) -> ast::Mod {
    let sess = parse::new_parse_sess();
    let qcx = QuoteCtxt::new("p", &sess);

    let bytes = limbs(p, 8);

    let mut items = Vec::new();

    let name = token::str_to_ident(name);
    let struct_item = quote_item!(&qcx.cx,
        pub struct $name(BigUint);
    ).expect("quote_item error");
    items.push(struct_item);

    let prime_str = p.to_string();
    let prime_str = token::intern_and_get_ident(&*prime_str);
    let prime_str = P(codemap::dummy_spanned(ast::LitStr(prime_str, ast::CookedStr)));
    let prime_str = P(ast::Expr {
        node: ast::ExprLit(prime_str),
        span: DUMMY_SP,
        id: ast::DUMMY_NODE_ID,
    });

    let prime = token::str_to_ident("P");
    let prime_item = quote_item!(&qcx.cx,
        pub const $prime: &'static str = $prime_str;
    ).expect("quote_item failed to create prime item");
    items.push(prime_item);

    let impl_item = quote_item!(&qcx.cx,
        impl $name {
            pub fn from_bytes_le(b: &[u8]) -> Option<$name> {
                use num::{Zero, One, Integer};
                use num::bigint::ToBigUint;
                let zero: BigUint = Zero::zero();
                let one: BigUint = One::one();
                let mut val = zero;
                for i in b.iter().rev() {
                    val = val << 8;
                    val = &val + &(*i).to_biguint().unwrap();
                }

                let p: BigUint = from_str($prime).unwrap();
                let val = val % p;
                Some($name(val))
            }

            pub fn to_bytes_le(&self) -> Vec<u8> {
                use num::{Zero, One, Integer};
                let zero: BigUint = Zero::zero();
                let one: BigUint = One::one();
                let limb_unit: BigUint = one << 8;
                let mut ret = Vec::new();

                let mut n = self.0.clone();
                for _ in (0..$bytes) {
                    let (new_n, limb) = n.div_mod_floor(&limb_unit);
                    n = new_n;
                    ret.push(limb.to_u8().unwrap());
                }
                ret
            }

            pub fn add(&self, b: &$name) -> $name {
                let p: BigUint = from_str($prime).unwrap();
                let c: BigUint = &self.0 + &b.0;
                let d: BigUint = c % p;
                $name(d)
            }

            pub fn double(&self) -> $name {
                // FIXME can be more efficient
                self.add(self)
            }

            pub fn sub(&self, b: &$name) -> $name {
                let p: BigUint = from_str($prime).unwrap();
                // prevent overflow
                let self_p: BigUint = &self.0 + &p;
                let c: BigUint = &self_p - &b.0;
                let d: BigUint = c % p;
                $name(d)
            }
        }
    ).expect("quote_item failed for impl");
    items.push(impl_item);

    let view_items = {
        // `extern crate num;`
        let view_item_extern = ast::ViewItem {
            node: ast::ViewItemExternCrate(token::str_to_ident("num"), None, ast::DUMMY_NODE_ID),
            attrs: Vec::new(),
            vis: ast::Inherited,
            span: DUMMY_SP,
        };

        // `use num::bigint::BigUint;`
        let segments = ["num", "bigint", "BigUint"].iter().map(|n| {
            ast::PathSegment {
                identifier: token::str_to_ident(*n),
                parameters: ast::PathParameters::none(),
            }
        }).collect();
        let parent = ast::Path {
            span: DUMMY_SP,
            global: false,
            segments: segments,
        };

        let id = token::str_to_ident("BigUint");
        let path = ast::ViewPathSimple(id, parent, ast::DUMMY_NODE_ID);
        let path = P(codemap::dummy_spanned(path));

        let view_item_use = ast::ViewItem {
            node: ast::ViewItemUse(path),
            attrs: Vec::new(),
            vis: ast::Inherited,
            span: DUMMY_SP,
        };

        vec!(view_item_extern, view_item_use)
    };

    ast::Mod {
        inner: DUMMY_SP,
        view_items: view_items,
        items: items,
    }
}
