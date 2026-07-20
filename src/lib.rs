//! NEXT — reference implementation.
//!
//! Build order (Compendium Part I; do not reorder): value layer → lexer/parser
//! → **oracle interpreter** → normalization + harness → (later) contracts.
//! This crate is currently at the value layer.

pub mod analyzer;
pub mod ast;
pub mod contract;
pub mod desugar;
pub mod env;
pub mod interner;
pub mod lex;
pub mod normalize;
pub mod oracle;
pub mod parse;
pub mod rational;
pub mod value;
