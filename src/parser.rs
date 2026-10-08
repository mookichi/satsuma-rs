//! DIMACS CNF parsing.
//!
//! Port of `parse_dimacs_to_cnf2wl` in `parser.h`. Accepts the same language:
//! comment lines starting with `c`, a single `p cnf <vars> <clauses>` header,
//! and whitespace-separated integer literals terminated by `0`.

use crate::cnf2wl::CnfWl;
use std::io::{self, Read};

/// Errors that can occur while parsing DIMACS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    /// No `p cnf` header was found before the first clause.
    MissingHeader,
    /// Malformed `p` line.
    InvalidHeader(String),
    /// A literal references a variable outside `1..=n_vars`.
    LiteralOutOfRange { lit: i32, n_vars: usize },
    /// Input ended inside a clause.
    UnexpectedEof,
    /// Generic syntax error.
    InvalidToken(String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::MissingHeader => {
                write!(f, "formula must begin with 'p cnf <vars> <clauses>' line")
            }
            ParseError::InvalidHeader(s) => write!(f, "invalid problem definition: {s}"),
            ParseError::LiteralOutOfRange { lit, n_vars } => {
                write!(f, "literal {lit} out of range for {n_vars} variables")
            }
            ParseError::UnexpectedEof => write!(f, "unexpected end of input inside a clause"),
            ParseError::InvalidToken(s) => write!(f, "can not parse: {s}"),
        }
    }
}

impl std::error::Error for ParseError {}

/// Parse DIMACS text into a [`CnfWl`].
pub fn parse_dimacs_str(text: &str) -> Result<CnfWl, ParseError> {
    let mut formula = CnfWl::new();
    let mut reserved = false;
    let mut n_vars = 0usize;
    let mut current: Vec<i32> = Vec::new();

    for raw_line in text.lines() {
        let line = raw_line.trim();
        if line.is_empty() {
            continue;
        }
        let first = line.as_bytes()[0] as char;
        match first {
            'c' | 'C' => continue,
            'p' | 'P' => {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() != 4 || !parts[1].eq_ignore_ascii_case("cnf") {
                    return Err(ParseError::InvalidHeader(line.to_string()));
                }
                n_vars = parts[2]
                    .parse::<usize>()
                    .map_err(|_| ParseError::InvalidHeader(line.to_string()))?;
                let n_clauses = parts[3]
                    .parse::<usize>()
                    .map_err(|_| ParseError::InvalidHeader(line.to_string()))?;
                formula.reserve(n_vars, n_clauses);
                reserved = true;
            }
            '-' | '0'..='9' => {
                if !reserved {
                    return Err(ParseError::MissingHeader);
                }
                for tok in line.split_whitespace() {
                    // Allow trailing comments after the clause terminator.
                    if tok.starts_with('c') || tok.starts_with('C') {
                        break;
                    }
                    // Skip `%` / `0` terminator lines of some DIMACS variants.
                    if tok == "%" {
                        current.clear();
                        break;
                    }
                    let lit: i32 = tok
                        .parse()
                        .map_err(|_| ParseError::InvalidToken(tok.to_string()))?;
                    if lit == 0 {
                        let clause = std::mem::take(&mut current);
                        check_range(&clause, n_vars)?;
                        formula.add_clause(&clause);
                    } else {
                        if lit.abs() as usize > n_vars {
                            return Err(ParseError::LiteralOutOfRange { lit, n_vars });
                        }
                        current.push(lit);
                    }
                }
            }
            _ => return Err(ParseError::InvalidToken(line.to_string())),
        }
    }
    if !current.is_empty() {
        return Err(ParseError::UnexpectedEof);
    }
    if !reserved {
        return Err(ParseError::MissingHeader);
    }
    Ok(formula)
}

fn check_range(clause: &[i32], n_vars: usize) -> Result<(), ParseError> {
    for &l in clause {
        if l.abs() as usize > n_vars {
            return Err(ParseError::LiteralOutOfRange { lit: l, n_vars });
        }
    }
    Ok(())
}

/// Parse DIMACS from a file path, or from stdin when `path` is `None`.
pub fn parse_dimacs_file(path: Option<&str>) -> Result<(CnfWl, usize), ParseError> {
    let text = match path {
        Some(p) => std::fs::read_to_string(p)
            .map_err(|e| ParseError::InvalidToken(format!("could not open file '{p}': {e}")))?,
        None => {
            let mut buf = String::new();
            io::stdin()
                .read_to_string(&mut buf)
                .map_err(|e| ParseError::InvalidToken(format!("could not read stdin: {e}")))?;
            buf
        }
    };
    let mb = text.len() / 1_000_000;
    Ok((parse_dimacs_str(&text)?, mb))
}

#[cfg(test)]
mod tests {
    use super::*;

    const PHP: &str = "c example\np cnf 2 2\n1 2 0\n-1 -2 0\n";

    #[test]
    fn parses_example() {
        let f = parse_dimacs_str(PHP).unwrap();
        assert_eq!(f.n_variables(), 2);
        assert_eq!(f.n_clauses(), 2);
    }

    #[test]
    fn rejects_missing_header() {
        assert_eq!(
            parse_dimacs_str("1 0\n").unwrap_err(),
            ParseError::MissingHeader
        );
    }

    #[test]
    fn rejects_out_of_range() {
        let err = parse_dimacs_str("p cnf 1 1\n2 0\n").unwrap_err();
        assert!(matches!(err, ParseError::LiteralOutOfRange { .. }));
    }
}
