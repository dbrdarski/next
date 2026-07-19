//! The `next` CLI — run a NEXT program and print its result.
//!
//! Usage:
//!   next <file.next>     run a program file
//!   next                 read a program from stdin
//!
//! `println`/`exit`/`readFile` host-effect doubles are available (the harness).
//! The value rendering below is a **debug/tooling** rendering, deliberately kept
//! out of the library: NEXT's own print doctrine (how structures stringify) is an
//! open design question (E11), so this is not it.

use std::io::Read;

use next::oracle::run_source;
use next::value::{ValueData, ValueRef};

fn main() {
    let src = match std::env::args().nth(1) {
        Some(path) => match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("next: cannot read `{path}`: {e}");
                std::process::exit(2);
            }
        },
        None => {
            let mut s = String::new();
            if std::io::stdin().read_to_string(&mut s).is_err() {
                eprintln!("next: failed to read stdin");
                std::process::exit(2);
            }
            s
        }
    };

    match run_source(&src) {
        Ok((value, io)) => {
            for line in io.output {
                println!("{line}");
            }
            if let Some(code) = io.exit_code {
                println!("(exit {code})");
            }
            println!("=> {}", render(&value));
        }
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    }
}

/// A debug rendering of a value (see the module note — not the language's print).
fn render(v: &ValueRef) -> String {
    match v.data() {
        ValueData::Boolean(b) => b.to_string(),
        ValueData::Null => "null".to_string(),
        ValueData::Number(n) => n.to_string(),
        ValueData::Str(u) => format!("{:?}", String::from_utf16_lossy(u)),
        ValueData::Tuple(items) => {
            let parts: Vec<String> = items.iter().map(render).collect();
            format!("[{}]", parts.join(", "))
        }
        ValueData::Record(entries) => {
            let parts: Vec<String> = entries
                .iter()
                .map(|e| format!("{}: {}", String::from_utf16_lossy(&e.key), render(&e.value)))
                .collect();
            format!("{{ {} }}", parts.join(", "))
        }
        ValueData::Function(_) => "<function>".to_string(),
        ValueData::Native(n) => format!("<native {}>", n.get().name),
        ValueData::Indeterminate(form) => form.label().to_string(),
    }
}
