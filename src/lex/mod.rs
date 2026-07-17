//! Lexing (Grammar Specification v0.1, §1): source text → token stream.

mod lexer;
pub mod token;

pub use lexer::{LexError, lex};
pub use token::{TemplateElem, Token, TokenKind};

#[cfg(test)]
mod tests;
