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

    fn is_pointer_sized(&self) -> bool {
        match *self {
            Primitive::Usize => true,
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

        let mut cast_asserts = vec![];
        let mut from_asserts = vec![];
        let mut try_from_asserts = vec![];

        for qy in qs.iter() {
            let qy_name = syn::Ident::from(format!("{}", qy));
            if qx.ibits() < qy.ibits() {
                cast_asserts.push(quote! {
                    assert_eq!(f64(#qx_name(#qy_name(0.5_f64).unwrap()).unwrap()), 0.5);
                });
                if cfg!(feature = "try-from") {
                    try_from_asserts.push(quote! {
                        assert_eq!(f64::from(#qx_name::try_from(#qy_name::try_from(0.5_f64).unwrap()).unwrap()), 0.5);
                    });
                }
            } else {
                cast_asserts.push(quote! {
                    assert_eq!(f64(#qx_name(#qy_name(0.5_f64).unwrap())), 0.5);
                });
                from_asserts.push(quote! {
                    assert_eq!(f64::from(#qx_name::from(#qy_name::try_from(0.5_f64).unwrap())), 0.5);
                });
            }
        }
        quote! {
            mod #test_name {
                use super::*;

                #[test]
                fn cast() {
                    #(#cast_asserts)*
                }

                #[test]
                fn from() {
                    #(#from_asserts)*
                }

                #[test]
                #[cfg(feature = "try-from")]
                fn try_from() {
                    #(#try_from_asserts)*
                }
            }
        }
    }).collect();
    let cross_tokens = quote! { #(#cross_tests)* };

    let file_path = Path::new(&out_dir).join("cross.rs");
    let mut f = File::create(&file_path).unwrap();
    f.write_all(cross_tokens.to_string().as_bytes()).unwrap();

    let _ = ::std::process::Command::new("rustfmt")
        .arg("--write-mode")
        .arg("overwrite")
        .arg(file_path.to_str().unwrap())
        .output();

    let to_ixx_tests: Vec<_> = qs.iter().flat_map(|q| {
        let test_name = syn::Ident::from(format!("i{}f{}", q.ibits(), q.fbits));
        let q_name = syn::Ident::from(format!("{}", q));

        let mut cast_asserts = vec![];
        let mut from_asserts = vec![];
        let mut try_from_asserts = vec![];

        for p in PRIMITIVES.iter() {
            let p_name = syn::Ident::from(format!("{}", p));
            let (f, i): (f64, u8) = if q.ibits() == 1 {
                (0.4, 0)
            } else {
                (1.1, 1)
            };
            if p.ibits() < q.ibits() || !p.is_ixx() {
                cast_asserts.push(quote! {
                    assert_eq!(#p_name(#q_name(#f).unwrap()).unwrap(), #i as #p_name);
                });
                if cfg!(feature = "try-from") && !p.is_pointer_sized() {
                    try_from_asserts.push(quote! {
                        assert_eq!(#p_name::try_from(#q_name::try_from(#f).unwrap()).unwrap(), #i as #p_name);
                    });
                }
            } else {
                cast_asserts.push(quote! {
                    assert_eq!(#p_name(#q_name(#f).unwrap()), #i as #p_name);
                });
                if !p.is_pointer_sized() {
                    from_asserts.push(quote! {
                        assert_eq!(#p_name::from(#q_name::try_from(#f).unwrap()), #i as #p_name);
                    });
                }
            }
        }
        quote! {
            mod #test_name {
                use super::*;

                #[test]
                fn cast() {
                    #(#cast_asserts)*
                }

                #[test]
                fn from() {
                    #(#from_asserts)*
                }

                #[test]
                #[cfg(feature = "try-from")]
                fn try_from() {
                    #(#try_from_asserts)*
                }
            }
        }
    }).collect();
    let to_ixx_tokens = quote! { #(#to_ixx_tests)* };

    let file_path = Path::new(&out_dir).join("to-ixx.rs");
    let mut f = File::create(&file_path).unwrap();
    f.write_all(to_ixx_tokens.to_string().as_bytes()).unwrap();

    let _ = ::std::process::Command::new("rustfmt")
        .arg("--write-mode")
        .arg("overwrite")
        .arg(file_path.to_str().unwrap())
        .output();

    let from_ixx_tests: Vec<_> = qs.iter().flat_map(|q| {
        let test_name = syn::Ident::from(format!("i{}f{}", q.ibits(), q.fbits));
        let q_name = syn::Ident::from(format!("{}", q));

        let mut cast_asserts = vec![];
        let mut from_asserts = vec![];
        let mut try_from_asserts = vec![];

        for p in PRIMITIVES.iter() {
            let p_name = syn::Ident::from(format!("{}", p));
            let i = if q.ibits() == 1 { 0 } else { 1 };
            if p.ibits() <= q.ibits() {
                cast_asserts.push(quote! {
                    assert_eq!(f64(#q_name(#i as #p_name)), #i as f64);
                });
                if !p.is_pointer_sized() {
                    from_asserts.push(quote! {
                        assert_eq!(f64::from(#q_name::from(#i as #p_name)), #i as f64);
                    });
                }
            } else {
                cast_asserts.push(quote! {
                    assert_eq!(f64(#q_name(#i as #p_name).unwrap()), #i as f64);
                });
                if cfg!(feature = "try-from") && !p.is_pointer_sized() {
                    try_from_asserts.push(quote! {
                        assert_eq!(f64::from(#q_name::try_from(#i as #p_name).unwrap()), #i as f64);
                    });
                }
            }
        }
        quote! {
            mod #test_name {
                use super::*;

                #[test]
                fn cast() {
                    #(#cast_asserts)*
                }

                #[test]
                fn from() {
                    #(#from_asserts)*
                }

                #[test]
                #[cfg(feature = "try-from")]
                fn try_from() {
                    #(#try_from_asserts)*
                }
            }
        }
    }).collect();
    let from_ixx_tokens = quote! { #(#from_ixx_tests)* };

    let file_path = Path::new(&out_dir).join("from-ixx.rs");
    let mut f = File::create(&file_path).unwrap();
    f.write_all(from_ixx_tokens.to_string().as_bytes()).unwrap();

    let _ = ::std::process::Command::new("rustfmt")
        .arg("--write-mode")
        .arg("overwrite")
        .arg(file_path.to_str().unwrap())
        .output();

    println!("cargo:rerun-if-changed=build.rs");
}
