use clap::{Parser, Subcommand};
use std::fs;
use std::path::PathBuf;

use koda_compiler::{Parser as KParser, typecheck, compile_with_llvm};

#[derive(Parser, Debug)]
#[command(name = "kodac")]
#[command(about = "Koda compiler (front-end draft)")]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Parse a source file and print a brief summary
    Parse { file: PathBuf },
    /// Parse and type-check a source file
    Check { file: PathBuf },
    /// Compile a source file using LLVM backend (requires feature)
    Compile { file: PathBuf },
}

fn main() {
    let cli = Cli::parse();
    match cli.command.unwrap_or(Command::Parse { file: PathBuf::from("testcase/main.koda") }) {
        Command::Parse { file } => {
            let src = fs::read_to_string(&file).expect("failed to read file");
            match KParser::from_source(&src).and_then(|mut p| p.parse_program()) {
                Ok(prog) => {
                    println!("Parsed OK: {} top-level statements", prog.stmts.len());
                    // For now print debug AST to help inspection
                    println!("{:#?}", prog);
                }
                Err(e) => {
                    eprintln!("Parse error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        Command::Check { file } => {
            let src = fs::read_to_string(&file).expect("failed to read file");
            match KParser::from_source(&src).and_then(|mut p| p.parse_program()) {
                Ok(prog) => {
                    match typecheck(&prog) {
                        Ok(()) => {
                            println!("Type check OK: {} top-level statements", prog.stmts.len());
                        }
                        Err(te) => {
                            eprintln!("Type error at {}:{}: {}", te.pos.line, te.pos.column, te.message);
                            std::process::exit(1);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("Parse error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        Command::Compile { file } => {
            let src = fs::read_to_string(&file).expect("failed to read file");
            match KParser::from_source(&src).and_then(|mut p| p.parse_program()) {
                Ok(prog) => {
                    match compile_with_llvm(&prog) {
                        Ok(()) => {
                            println!("Compile OK (LLVM); output not yet emitted in this stub");
                        }
                        Err(e) => {
                            eprintln!("Compile error: {}", e);
                            eprintln!("Hint: build with --features koda-compiler/llvm to enable the LLVM backend");
                            std::process::exit(1);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("Parse error: {}", e);
                    std::process::exit(1);
                }
            }
        }
    }
}
