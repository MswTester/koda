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
fn method_casts_basic() {
    // number -> string
    check_ok("print(1.string())\n");
    check_ok("x: u32 = 10\nprint(x.string())\n");

    // int literal -> numeric
    check_ok("x: i32 = 1.i32()\n");
    check_ok("y: u32 = 1.u32()\n");
    check_ok("z: f32 = 1.f32()\n");

    // bool -> string
    check_ok("print(true.string())\n");
}

#[test]
fn method_casts_numeric_between() {
    // explicit casts allowed between numeric types
    check_ok("x: i32 = 1.u32().i32()\n");
    check_ok("y: f32 = 1.i32().f32()\n");
    check_ok("z: u32 = 1.f32().u32()\n");
}

#[test]
fn method_casts_invalid() {
    // string to numeric is not allowed
    check_err("x: i32 = \"hi\".i32()\n");
    check_err("y: u32 = \"hi\".u32()\n");
    check_err("z: f32 = \"hi\".f32()\n");
}

#[test]
fn as_casts_basic() {
    check_ok("x: i32 = 1 as i32\n");
    check_ok("y: u32 = 1 as u32\n");
    check_ok("z: f32 = 1 as f32\n");
    check_ok("s: string = true as string\n");
}

#[test]
fn as_casts_numeric_between() {
    check_ok("x: i32 = (1 as u32) as i32\n");
    check_ok("y: f32 = (1 as i32) as f32\n");
    check_ok("z: u32 = (1 as f32) as u32\n");
}

#[test]
fn as_casts_invalid() {
    check_err("x: i32 = \"hi\" as i32\n");
    check_err("z: f32 = \"hi\" as f32\n");
}

#[test]
fn numeric_unary_and_ops_with_f32() {
    // unary neg on numeric
    check_ok("x: f32 = (-1).f32()\n");

    // disallow implicit int<->float arithmetic
    check_err("x = 1 + 2.f32()\n");
    check_err("x = 1.f32() * 2\n");

    // allow float+float
    check_ok("x: f32 = 1.f32() + 2.f32()\n");
}
