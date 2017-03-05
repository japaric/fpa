use super::*;

#[test]
fn fmt() {
    assert_eq!(format!("{}", f1p15::MIN), "-1");
    assert_eq!(format!("{}", F1P15(-0.5_f64).unwrap()), "-0.5");
    assert_eq!(format!("{}", F1P15(-0.000030517578125_f64).unwrap()),
               "-0.000030517578125");
    assert_eq!(format!("{}", F1P15(-0f64).unwrap()), "0");
    assert_eq!(format!("{}", F1P15(0f64).unwrap()), "0");
    assert_eq!(format!("{}", F1P15(0.000030517578125_f64).unwrap()),
               "0.000030517578125");
    assert_eq!(format!("{}", F1P15(0.5_f64).unwrap()), "0.5");
    assert_eq!(format!("{}", f1p15::MAX), "0.999969482421875");

    assert_eq!(format!("{}", f1p7::MIN), "-1");
    assert_eq!(format!("{}", F1P7(-0.5_f64).unwrap()), "-0.5");
    assert_eq!(format!("{}", F1P7(-0.0078125_f64).unwrap()), "-0.0078125");
    assert_eq!(format!("{}", F1P7(-0f64).unwrap()), "0");
    assert_eq!(format!("{}", F1P7(0f64).unwrap()), "0");
    assert_eq!(format!("{}", F1P7(0.0078125_f64).unwrap()), "0.0078125");
    assert_eq!(format!("{}", F1P7(0.5_f64).unwrap()), "0.5");
    assert_eq!(format!("{}", f1p7::MAX), "0.9921875");

    assert_eq!(format!("{}", f16p16::MIN), "-32768");
    assert_eq!(format!("{}", F16P16(-1.5_f64).unwrap()), "-1.5");
    assert_eq!(format!("{}", F16P16(-1f64).unwrap()), "-1");
    assert_eq!(format!("{}", F16P16(-0.5_f64).unwrap()), "-0.5");
    assert_eq!(format!("{}", F16P16(-0.0000152587890625_f64).unwrap()),
               "-0.0000152587890625");
    assert_eq!(format!("{}", F16P16(-0f64).unwrap()), "0");
    assert_eq!(format!("{}", F16P16(0f64).unwrap()), "0");
    assert_eq!(format!("{}", F16P16(0.0000152587890625_f64).unwrap()),
               "0.0000152587890625");
    assert_eq!(format!("{}", F16P16(0.5_f64).unwrap()), "0.5");
    assert_eq!(format!("{}", F16P16(1f64).unwrap()), "1");
    assert_eq!(format!("{}", F16P16(1.5_f64).unwrap()), "1.5");
    assert_eq!(format!("{}", f16p16::MAX), "32767.9999847412109375");

    assert_eq!(format!("{}", f24p8::MIN), "-8388608");
    assert_eq!(format!("{}", F24P8(-1.5_f64).unwrap()), "-1.5");
    assert_eq!(format!("{}", F24P8(-1f64).unwrap()), "-1");
    assert_eq!(format!("{}", F24P8(-0.5_f64).unwrap()), "-0.5");
    assert_eq!(format!("{}", F24P8(-0.00390625_f64).unwrap()),
               "-0.00390625");
    assert_eq!(format!("{}", F24P8(-0f64).unwrap()), "0");
    assert_eq!(format!("{}", F24P8(0f64).unwrap()), "0");
    assert_eq!(format!("{}", F24P8(0.00390625_f64).unwrap()), "0.00390625");
    assert_eq!(format!("{}", F24P8(0.5_f64).unwrap()), "0.5");
    assert_eq!(format!("{}", F24P8(1f64).unwrap()), "1");
    assert_eq!(format!("{}", F24P8(1.5_f64).unwrap()), "1.5");
    assert_eq!(format!("{}", f24p8::MAX), "8388607.99609375");

    assert_eq!(format!("{}", uf0p8::MIN), "0");
    assert_eq!(format!("{}", UF0P8(0_f64).unwrap()), "0");
    assert_eq!(format!("{}", UF0P8(0.00390625_f64).unwrap()), "0.00390625");
    assert_eq!(format!("{}", UF0P8(0.25_f64).unwrap()), "0.25");
    assert_eq!(format!("{}", UF0P8(0.5_f64).unwrap()), "0.5");
    assert_eq!(format!("{}", uf0p8::MAX), "0.99609375");

    assert_eq!(format!("{}", uf0p16::MIN), "0");
    assert_eq!(format!("{}", UF0P16(0_f64).unwrap()), "0");
    assert_eq!(format!("{}", UF0P16(0.0000152587890625_f64).unwrap()),
               "0.0000152587890625");
    assert_eq!(format!("{}", UF0P16(0.25_f64).unwrap()), "0.25");
    assert_eq!(format!("{}", UF0P16(0.5_f64).unwrap()), "0.5");
    assert_eq!(format!("{}", uf0p16::MAX), "0.9999847412109375");

    assert_eq!(format!("{}", uf16p16::MIN), "0");
    assert_eq!(format!("{}", UF16P16(0_f64).unwrap()), "0");
    assert_eq!(format!("{}", UF16P16(0.0000152587890625_f64).unwrap()),
               "0.0000152587890625");
    assert_eq!(format!("{}", UF16P16(1f64).unwrap()), "1");
    assert_eq!(format!("{}", UF16P16(1.5_f64).unwrap()), "1.5");
    assert_eq!(format!("{}", uf16p16::MAX), "65535.9999847412109375");

    assert_eq!(format!("{}", uf24p8::MIN), "0");
    assert_eq!(format!("{}", UF24P8(0_f64).unwrap()), "0");
    assert_eq!(format!("{}", UF24P8(0.00390625_f64).unwrap()), "0.00390625");
    assert_eq!(format!("{}", UF24P8(0.5_f64).unwrap()), "0.5");
    assert_eq!(format!("{}", UF24P8(1_f64).unwrap()), "1");
    assert_eq!(format!("{}", UF24P8(1.5_f64).unwrap()), "1.5");
    assert_eq!(format!("{}", uf24p8::MAX), "16777215.99609375");
}

#[test]
fn limits() {
    F1P15(-1_f32).unwrap();
    F1P15(-1_f64).unwrap();
    assert!(F1P15(1_f32).is_err());
    assert!(F1P15(1_f64).is_err());

    F1P7(-1_f32).unwrap();
    F1P7(-1_f64).unwrap();
    assert!(F1P7(1_f32).is_err());
    assert!(F1P7(1_f64).is_err());

    F16P16(-32768_f32).unwrap();
    F16P16(-32768_f64).unwrap();
    // assert!(F16P16(32768_f32).is_err());
    assert!(F16P16(32768_f64).is_err());

    F24P8(-8388608_f32).unwrap();
    F24P8(-8388608_f64).unwrap();
    // assert!(F24P8(8388608_f32).is_err());
    assert!(F24P8(8388608_f64).is_err());

    UF0P16(0_f32).unwrap();
    UF0P16(0_f64).unwrap();
    assert!(UF0P16(1_f32).is_err());
    assert!(UF0P16(1_f64).is_err());

    UF0P8(0_f32).unwrap();
    UF0P8(0_f64).unwrap();
    assert!(UF0P8(1_f32).is_err());
    assert!(UF0P8(1_f64).is_err());

    UF16P16(0_f32).unwrap();
    UF16P16(0_f64).unwrap();
    // assert!(UF16P16(32768_f32).is_err());
    assert!(UF16P16(65536_f64).is_err());

    UF24P8(0_f32).unwrap();
    UF24P8(0_f64).unwrap();
    // assert!(UF24P8(8388608_f32).is_err());
    assert!(UF24P8(16777216_f64).is_err());
}
