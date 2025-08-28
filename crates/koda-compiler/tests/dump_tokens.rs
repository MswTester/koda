use std::fs;
use std::path::PathBuf;

use koda_compiler::{Lexer, TokenKind};

#[test]
fn dump_tokens_around_line_7_to_13() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testcase/main.koda");
    let src = fs::read_to_string(&path).expect("failed to read testcase/main.koda");
    let mut lex = Lexer::new(&src);
    let mut toks = Vec::new();
    loop {
        let t = lex.next_token().expect("lex ok");
        toks.push(t.clone());
        if t.kind == TokenKind::Eof { break; }
    }
    // print all tokens with line/col
    for (i, t) in toks.iter().enumerate() {
        println!("{:03} {:?} at {}:{}", i, t.kind, t.pos.line, t.pos.column);
    }
    assert!(true);
}
