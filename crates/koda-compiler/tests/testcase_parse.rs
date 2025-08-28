use std::fs;
use std::path::PathBuf;

use koda_compiler::Parser;

#[test]
fn parse_repository_testcase_main_koda() {
    // crates/koda-compiler -> repo root -> testcase/main.koda
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testcase/main.koda");
    let src = fs::read_to_string(&path).expect("failed to read testcase/main.koda");
    let mut p = Parser::from_source(&src).expect("lexer ok");
    let prog = p.parse_program();
    if let Err(e) = &prog {
        panic!("parse error: {}", e);
    }
}
