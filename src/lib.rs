//! NEXT — reference implementation.
//!
//! Build order (Compendium Part I; do not reorder): value layer → lexer/parser
//! → **oracle interpreter** → normalization + harness → (later) contracts.
//! This crate is currently at the value layer.

pub mod ast;
pub mod interner;
pub mod lex;
pub mod parse;
pub mod rational;
pub mod value;
