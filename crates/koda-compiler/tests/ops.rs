use koda_compiler::{Parser as KParser, typecheck};

fn check_ok(src: &str) {
    let mut p = KParser::from_source(src).expect("lex/parse failed to start");
    let prog = p.parse_program().expect("parse error");
    typecheck(&prog).expect("typecheck expected OK");
}

fn check_err(src: &str) {
    let mut p = KParser::from_source(src).expect("lex/parse failed to start");
    let prog = p.parse_program().expect("parse error");
    assert!(typecheck(&prog).is_err(), "typecheck should fail but succeeded");
}

#[test]
fn binary_ops_mod_bitwise_shifts() {
    // modulo on integers
    check_ok("x: u32 = 5 % 2\n");
    check_ok("x: i32 = 5 % 2\n");
    // modulo not allowed on floats
    check_err("x: f32 = 1.f32() % 2.f32()\n");

    // bitwise ops on integers
    check_ok("x: u32 = 1 & 2\n");
    check_ok("y: i32 = 1 | 2\n");
    check_ok("z: u32 = 1 ^ 2\n");
    // bitwise not allowed on floats
    check_err("x: f32 = 1.f32() & 2.f32()\n");

    // shifts: left type preserved, right must be integer
    check_ok("x: i32 = 1.i32() << 2\n");
    check_ok("y: u32 = 1 << 2\n");
    check_ok("z: u32 = 8 >> 1\n");
    // shifts with floats are invalid
    check_err("x: f32 = 1.f32() << 2\n");
    check_err("x: u32 = 1 << 2.f32()\n");
}

#[test]
fn logical_ops_and_or() {
    check_ok("b: bool = true && false\n");
    check_ok("b: bool = true || false\n");
    // non-bool operands invalid
    check_err("x: bool = 1 && 0\n");
    check_err("x: bool = 1 || 0\n");
}

#[test]
fn comparison_ops_numeric() {
    check_ok("b: bool = 1 < 2\n");
    check_ok("b: bool = 1.i32() <= 2.i32()\n");
    check_ok("b: bool = 1.f32() > 2.f32()\n");
    // mixed int/float comparisons are not allowed implicitly
    check_err("b: bool = 1 < 2.f32()\n");
}

#[test]
fn compound_assign_arith() {
    check_ok("x: u32 = 0\nx += 1\n");
    check_ok("y: i32 = 10\ny -= 2\n");
    check_ok("z: f32 = 3.f32()\nz *= 2.f32()\n");
    check_ok("w: u32 = 8\nw /= 2\n");
}

#[test]
fn compound_assign_integer_specific() {
    // modulo compound on integers
    check_ok("x: i32 = 5\nx %= 2\n");
    // invalid on floats
    check_err("x: f32 = 5.f32()\nx %= 2.f32()\n");

    // bitwise compound on integers
    check_ok("a: u32 = 1\na &= 1\n");
    check_ok("b: i32 = 1\nb |= 2\n");
    check_ok("c: u32 = 1\nc ^= 3\n");

    // shifts compound on integers
    check_ok("d: i32 = 1\nd <<= 2\n");
    check_ok("e: u32 = 8\ne >>= 1\n");

    // invalid with floats
    check_err("f: f32 = 1.f32()\nf <<= 1\n");
}

#[test]
fn compound_assign_logical_and_or() {
    check_ok("b: bool = true\nb &&= false\n");
    check_ok("c: bool = true\nc ||= false\n");
    // invalid with non-bools
    check_err("x: u32 = 1\nx &&= 0\n");
}

#[test]
fn nullish_assign_errors() {
    // LHS must be Option<T>; using non-Option should error
    check_err("x: i32 = 1\nx ??= 2\n");
}
