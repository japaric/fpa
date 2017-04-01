use std::{env, fmt};
use std::io::Write;
use std::fs::File;
use std::path::PathBuf;

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

    let mut buffer = String::new();

    buffer.push_str("#[test]");
    buffer.push_str("fn cross() {");
    for qx in &qs {
        for qy in &qs {
            // more legible but chokes rustc
            // buffer.push_str(&format!("let qx = {}(0.5_f64).unwrap();\n", qx));
            // if qy.ibits() < qx.ibits() {
            //     buffer.push_str(&format!("let qy = {}(qx).unwrap();\n", qy));
            // } else {
            //     buffer.push_str(&format!("let qy = {}(qx);\n", qy));
            // }
            // buffer.push_str(&format!("assert_eq!(f64(qy), 0.5);\n"));

            if qy.ibits() < qx.ibits() {
                buffer.push_str(&format!("assert_eq!(f64({}({}(0.5_f64).unwrap()).unwrap()), 0.5);\n", qy, qx));
            } else {
                buffer.push_str(&format!("assert_eq!(f64({}({}(0.5_f64).unwrap())), 0.5);\n", qy, qx));
            }
        }
    }
    buffer.push_str("}");

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let mut f = File::create(out_dir.join("cross.rs")).unwrap();
    f.write_all(buffer.as_bytes()).unwrap();

    buffer.clear();
    buffer.push_str("#[test]");
    buffer.push_str("fn to_ixx() {");
    for q in &qs {
        for p in &PRIMITIVES {
            let (f, i) = if q.ibits() == 1 {
                (0.4, 0)
            } else {
                (1.1, 1)
            };

            if p.ibits() < q.ibits() || !p.is_ixx() {
                buffer.push_str(&format!("assert_eq!({}({}({}_f64).unwrap()).unwrap(), {});\n", p, q, f, i));
            } else {
                buffer.push_str(&format!("assert_eq!({}({}({}_f64).unwrap()), {});\n", p, q, f, i));
            }
        }
    }
    buffer.push_str("}");
    let mut f = File::create(out_dir.join("to-ixx.rs")).unwrap();
    f.write_all(buffer.as_bytes()).unwrap();

    buffer.clear();
    buffer.push_str("#[test]");
    buffer.push_str("fn from_ixx() {");
    for q in &qs {
        for p in &PRIMITIVES {
            let i = if q.ibits() == 1 {
                0
            } else {
                1
            };

            if p.ibits() <= q.ibits() {
                buffer.push_str(&format!("assert_eq!(f64({}({}_{})), {1}.);\n", q, i, p));
            } else {
                buffer.push_str(&format!("assert_eq!(f64({}({}_{}).unwrap()), {1}.);\n", q, i, p));
            }
        }
    }
    buffer.push_str("}");
    let mut f = File::create(out_dir.join("from-ixx.rs")).unwrap();
    f.write_all(buffer.as_bytes()).unwrap();

    println!("cargo:rerun-if-changed=build.rs");
}
