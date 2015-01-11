use std::num::ToPrimitive;
use num::{BigUint, One, Zero, Integer};
use syntax::ast;
use syntax::codemap::DUMMY_SP;
use syntax::codemap::{ExpnInfo, NameAndSpan, MacroBang};
use syntax::ext::base;
use syntax::ext::expand::ExpansionConfig;
use syntax::parse::ParseSess;
use syntax::parse::token;
use syntax::ptr::P;

pub fn biguint_to_vec(n: &BigUint, limb_size: u8) -> Vec<u64> {
    let zero: BigUint = Zero::zero();
    let one: BigUint = One::one();
    let limb_unit: BigUint = one << (limb_size as usize);
    let mut ret = Vec::new();

    let mut n = n.clone();
    while n > zero {
        let (new_n, limb) = n.div_mod_floor(&limb_unit);
        n = new_n;
        ret.push(limb.to_u64().unwrap());
    }
    ret
}

pub fn slice_to_expr(v: &[u64]) -> P<ast::Expr> {
    let exprs = v.iter().map(|limb| {
        let val = ast::Lit {
            node: ast::LitInt(*limb, ast::UnsuffixedIntLit(ast::Plus)),
            span: DUMMY_SP,
        };
        P(ast::Expr {
            id: ast::DUMMY_NODE_ID,
            node: ast::ExprLit(P(val)),
            span: DUMMY_SP,
        })
    }).collect();
    P(ast::Expr {
        id: ast::DUMMY_NODE_ID,
        node: ast::ExprVec(exprs),
        span: DUMMY_SP,
    })
}

/// compute the number of limbs required for given prime `p`.
pub fn limbs(p: &BigUint, limb_size: u8) -> u8 {
    (p.bits() as u8 + limb_size - 1) / (limb_size as u8)
}

// `limb_unit^(limb * len) / p`
pub fn barrett_constant(p: &BigUint, limb_bit_size: u8, len: u8) -> BigUint {
    let one: BigUint = One::one();

    let len = len as usize;
    let limb_bit_size = limb_bit_size as usize;

    let n2k = one << (len * limb_bit_size * 2);
    &n2k / p
}

pub fn str_to_ty(s: &str) -> ast::Ty {
    let ty = ast::Path {
        span: DUMMY_SP,
        global: false,
        segments: vec!(
            ast::PathSegment {
                identifier: token::str_to_ident(s),
                parameters: ast::PathParameters::none(),
            }
        ),
    };
    ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: ast::TyPath(ty, ast::DUMMY_NODE_ID),
        span: DUMMY_SP,
    }
}

pub fn size_to_ty(size: u8) -> ast::Ty {
    let s = match size {
        8 => "u8",
        16 => "u16",
        32 => "u32",
        64 => "u64",
        _ => panic!("unsupported limb size: {}", size),
    };
    str_to_ty(s)
}

pub struct QuoteCtxt<'a> {
    pub sess: &'a ParseSess,
    pub cx: base::ExtCtxt<'a>,
}

impl<'a> QuoteCtxt<'a> {
    pub fn new(name: &str, sess: &'a ParseSess) -> QuoteCtxt<'a> {
        let cfg = ExpansionConfig {
            crate_name: name.to_string(),
            enable_quotes: true,
            recursion_limit: 64,
        };
        let mut ext_cx = base::ExtCtxt::new(sess, Vec::new(), cfg);
        // top span seems necessary. TODO: understand it properly
        ext_cx.bt_push(ExpnInfo {
            call_site: DUMMY_SP,
            callee: NameAndSpan { name: String::new(), format: MacroBang, span: None }
        });

        QuoteCtxt {
            sess: sess,
            cx: ext_cx,
        }
    }
}
