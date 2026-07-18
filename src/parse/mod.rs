//! Parsing (Grammar Specification v0.1, §§2–5): token stream → surface AST.

pub mod parser;
pub mod surface;

pub use parser::{ParseError, parse_expression, parse_program};

/// Contextual keywords (§1.3). These are ordinary identifiers everywhere except
/// the specific seats §§2–5 define; the parser commits on them only there.
pub mod token_kw {
    pub const MODULE: &str = "module";
    pub const IMPORT: &str = "import";
    pub const EXPORT: &str = "export";
    pub const FROM: &str = "from";
    pub const WHEN: &str = "when";
    pub const WHERE: &str = "where";
}

#[cfg(test)]
mod tests;
