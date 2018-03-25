#[macro_use]
extern crate quote;
extern crate syn;

use std::{env, fmt};
use std::io::Write;
use std::fs::File;
use std::path::{Path, PathBuf};

struct Q {
    bits: u8,
    fbits: u8,
}

impl Q {
    fn ibits(&self) -> u8 {
        self.bits - self.fbits
    }
}

impl fmt::Display for Q {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "I{}F{}", self.ibits(), self.fbits)
    }
}

enum Primitive {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
}

impl Primitive {
    fn ibits(&self) -> u8 {
        match *self {
            Primitive::I8 => 8,
            Primitive::I16 => 16,
            Primitive::I32 => 32,
            Primitive::I64 => 64,
            Primitive::Isize => 64,
            Primitive::U8 => 9,
            Primitive::U16 => 17,
            Primitive::U32 => 33,
            Primitive::U64 => 65,
            Primitive::Usize => 65,
        }
    }

    fn is_ixx(&self) -> bool {
        match *self {
            Primitive::I8 => true,
            Primitive::I16 => true,
            Primitive::I32 => true,
            Primitive::I64 => true,
            Primitive::Isize => true,
            _ => false,
        }
    }
}

impl fmt::Display for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            Primitive::I8 => "i8",
            Primitive::I16 => "i16",
            Primitive::I32 => "i32",
            Primitive::I64 => "i64",
            Primitive::Isize => "isize",
            Primitive::U8 => "u8",
            Primitive::U16 => "u16",
            Primitive::U32 => "u32",
            Primitive::U64 => "u64",
            Primitive::Usize => "usize",
        };

        f.write_str(s)
    }
}

const PRIMITIVES: [Primitive; 10] = [
    Primitive::I8,
    Primitive::I16,
    Primitive::I32,
    Primitive::I64,
    Primitive::Isize,
    Primitive::U8,
    Primitive::U16,
    Primitive::U32,
    Primitive::U64,
    Primitive::Usize,
];

fn main() {
    let mut qs = vec![];
    for bits in &[8, 16, 32] {
        for fbits in 1..*bits {
            qs.push(
                Q {
                    bits: *bits,
                    fbits: fbits,
                },
            )
        }
    }

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let cross_tests: Vec<_> = qs.iter().flat_map(|qx| {
        let test_name = syn::Ident::from(format!("i{}f{}", qx.ibits(), qx.fbits));
        let qx_name = syn::Ident::from(format!("{}", qx));
        let asserts: Vec<_> = qs.iter().map(move |qy| {
            let qy_name = syn::Ident::from(format!("{}", qy));
            if qx.ibits() < qy.ibits() {
                quote! {
                    assert_eq!(f64(#qx_name(#qy_name(0.5_f64).unwrap()).unwrap()), 0.5);
                }
            } else {
                quote! {
                    assert_eq!(f64(#qx_name(#qy_name(0.5_f64).unwrap())), 0.5);
                }
            }
        }).collect();
        quote! {
            #[test]
            fn #test_name() {
                #(#asserts)*
            }
        }
    }).collect();
    let cross_tokens = quote! { #(#cross_tests)* };

    let file_path = Path::new(&out_dir).join("cross.rs");
    let mut f = File::create(&file_path).unwrap();
    f.write_all(cross_tokens.to_string().as_bytes()).unwrap();

    let to_ixx_tests: Vec<_> = qs.iter().flat_map(|q| {
        let test_name = syn::Ident::from(format!("i{}f{}", q.ibits(), q.fbits));
        let q_name = syn::Ident::from(format!("{}", q));
        let asserts: Vec<_> = PRIMITIVES.iter().map(move |p| {
            let p_name = syn::Ident::from(format!("{}", p));
            let (f, i): (f64, u8) = if q.ibits() == 1 {
                (0.4, 0)
            } else {
                (1.1, 1)
            };
            if p.ibits() < q.ibits() || !p.is_ixx() {
                quote! {
                    assert_eq!(#p_name(#q_name(#f).unwrap()).unwrap(), #i as #p_name);
                }
            } else {
                quote! {
                    assert_eq!(#p_name(#q_name(#f).unwrap()), #i as #p_name);
                }
            }
        }).collect();
        quote! {
            #[test]
            fn #test_name() {
                #(#asserts)*
            }
        }
    }).collect();
    let to_ixx_tokens = quote! { #(#to_ixx_tests)* };

    let file_path = Path::new(&out_dir).join("to-ixx.rs");
    let mut f = File::create(&file_path).unwrap();
    f.write_all(to_ixx_tokens.to_string().as_bytes()).unwrap();

    let from_ixx_tests: Vec<_> = qs.iter().flat_map(|q| {
        let test_name = syn::Ident::from(format!("i{}f{}", q.ibits(), q.fbits));
        let q_name = syn::Ident::from(format!("{}", q));
        let asserts: Vec<_> = PRIMITIVES.iter().map(move |p| {
            let p_name = syn::Ident::from(format!("{}", p));
            let i = if q.ibits() == 1 {
                0
            } else {
                1
            };
            if p.ibits() <= q.ibits() {
                quote! {
                    assert_eq!(f64(#q_name(#i as #p_name)), #i as f64);
                }
            } else {
                quote! {
                    assert_eq!(f64(#q_name(#i as #p_name).unwrap()), #i as f64);
                }
            }
        }).collect();
        quote! {
            #[test]
            fn #test_name() {
                #(#asserts)*
            }
        }
    }).collect();
    let from_ixx_tokens = quote! { #(#from_ixx_tests)* };

    let file_path = Path::new(&out_dir).join("from-ixx.rs");
    let mut f = File::create(&file_path).unwrap();
    f.write_all(from_ixx_tokens.to_string().as_bytes()).unwrap();

    println!("cargo:rerun-if-changed=build.rs");
}
