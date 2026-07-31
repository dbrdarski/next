//! The `next` CLI — run a NEXT program and print its result.
//!
//! Usage:
//!   next <file.next>            run a program file
//!   next --check <file.next>    analyze a program without running it
//!   next                        read a program from stdin
//!
//! `println`/`exit`/`readFile` host-effect doubles are available (the harness).
//! The value rendering below is a **debug/tooling** rendering, deliberately kept
//! out of the library: NEXT's own print doctrine (how structures stringify) is an
//! open design question (E11), so this is not it.

use std::io::Read;

use next::analyzer::Severity;
use next::oracle::{check_source, run_source};
use next::value::{ValueData, ValueRef};

fn main() {
    let mut args = std::env::args().skip(1);
    let mut check = false;
    let mut path = args.next();
    if path.as_deref() == Some("--check") {
        check = true;
        path = args.next();
    }

    let src = match path {
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

    if check {
        return run_check(&src);
    }

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

/// Analyze without running: report every finding, and exit non-zero if the module is
/// rejected. A rejected module is a **compile error** — safety-unproven included, which
/// late-resolution §5 makes un-suppressible.
fn run_check(src: &str) {
    let verdict = match check_source(src) {
        Ok((v, _)) => v,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    };

    for f in &verdict.findings {
        let tier = match f.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        eprintln!("{tier}: [{:?}] {}", f.class, f.message);
    }
    for (name, c) in &verdict.owed_return_checks {
        eprintln!("note: return contract of `{name}` ({c:?}) is not yet checked — demand core owed");
    }

    if verdict.accepted() {
        println!("ok");
    } else {
        std::process::exit(1);
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
