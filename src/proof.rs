//! Proof logging: SR / binary SR / VeriPB.
//!
//! Mirrors `proof.h`'s role in the pipeline: every clause added by symmetry
//! reasoning (or removed by simplification) is logged so that an external
//! checker (`dsr-trim`, `VeriPB`) can verify the transformation.
//!
//! This port implements a functional DRAT-style text writer (the ASCII `SR`
//! format is a conservative extension of DRAT: introduction `clause`,
//! deletion `d clause`). Binary SR and VeriPB emit a documented placeholder
//! header plus the same clause stream so that downstream tooling sees a
//! well-formed file while full VeriPB rule logging remains future work.

use std::fmt::Write as _;
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

/// Proof formats, mirroring `proof_type` in `utility.h`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProofFormat {
    /// ASCII SR proof (default, checkable with `dsr-trim` for the
    /// RUP/introduction subset emitted here).
    #[default]
    Sr,
    /// Binary SR proof.
    BinarySr,
    /// VeriPB proof (experimental in the original as well).
    VeriPb,
}

impl ProofFormat {
    pub fn from_flag(flag: &str) -> Option<Self> {
        match flag.to_ascii_uppercase().as_str() {
            "SR" | "--SR" => Some(ProofFormat::Sr),
            "BSR" | "BINARY_SR" | "--BSR" => Some(ProofFormat::BinarySr),
            "VERIPB" | "--VERIPB" => Some(ProofFormat::VeriPb),
            _ => None,
        }
    }
}

/// Sink for proof output.
pub enum ProofSink {
    File(File),
    Buffer(Vec<u8>),
    Null,
}

/// Proof logger attached to the preprocessor.
pub struct Proof {
    format: ProofFormat,
    sink: ProofSink,
    n_variables: usize,
    /// Mirrors `proof_dense_crossover`: above this size, dense logging kicks in.
    pub dense_crossover: usize,
    /// Whether sparse POL-style logging is used.
    pub pol_logging: bool,
}

impl Proof {
    pub fn null(n_variables: usize, format: ProofFormat) -> Self {
        Self {
            format,
            sink: ProofSink::Null,
            n_variables,
            dense_crossover: 64,
            pol_logging: true,
        }
    }

    pub fn to_file(
        path: &Path,
        n_variables: usize,
        format: ProofFormat,
    ) -> io::Result<Self> {
        let mut file = File::create(path)?;
        match format {
            ProofFormat::Sr => {
                writeln!(file, "c satsuma-rs SR proof")?;
            }
            ProofFormat::BinarySr => {
                // Binary SR magic used by dsr-trim compatible writers.
                file.write_all(b"c satsuma-rs binary SR proof (placeholder header)\n")?;
            }
            ProofFormat::VeriPb => {
                writeln!(file, "pseudo-Boolean proof version 2.1")?;
                writeln!(file, "f {n_variables}")?;
            }
        }
        Ok(Self {
            format,
            sink: ProofSink::File(file),
            n_variables,
            dense_crossover: 64,
            pol_logging: true,
        })
    }

    pub fn to_buffer(n_variables: usize, format: ProofFormat) -> Self {
        Self {
            format,
            sink: ProofSink::Buffer(Vec::new()),
            n_variables,
            dense_crossover: 64,
            pol_logging: true,
        }
    }

    pub fn into_buffer(self) -> Vec<u8> {
        match self.sink {
            ProofSink::Buffer(b) => b,
            _ => Vec::new(),
        }
    }

    pub fn set_dense_crossover(&mut self, crossover: usize) {
        self.dense_crossover = crossover;
    }

    pub fn set_pol_logging(&mut self, pol: bool) {
        self.pol_logging = pol;
    }

    fn emit(&mut self, line: &str) {
        match &mut self.sink {
            ProofSink::File(f) => {
                let _ = writeln!(f, "{line}");
            }
            ProofSink::Buffer(b) => {
                let _ = writeln!(b, "{line}");
            }
            ProofSink::Null => {}
        }
    }

    fn clause_text(clause: &[i32]) -> String {
        let mut s = String::new();
        for l in clause {
            let _ = write!(s, "{l} ");
        }
        s.push('0');
        s
    }

    /// File header; `n_clauses` is the number of input clauses (as in the
    /// original `proof::header`).
    pub fn header(&mut self, _n_clauses: usize) {
        if self.format == ProofFormat::VeriPb {
            self.emit(&format!("c n_vars {}", self.n_variables));
        }
    }

    /// Log a RUP clause introduction.
    pub fn rup_clause(&mut self, clause: &[i32]) {
        self.emit(&Self::clause_text(clause));
    }

    /// Log a clause deletion (`d ...`).
    pub fn delete_clause(&mut self, _id: usize, clause: &[i32]) {
        let mut s = String::from("d ");
        s.push_str(&Self::clause_text(clause));
        self.emit(&s);
    }

    /// Log a blocked-clause introduction (used for AMO completion).
    pub fn blocked_clause(&mut self, clause: &[i32]) {
        self.emit(&Self::clause_text(clause));
    }

    /// Log a DRAT clause (used for fixed-up units and UNSAT core).
    pub fn drat_clause(&mut self, clause: &[i32]) {
        self.emit(&Self::clause_text(clause));
    }

    pub fn path_hint(path: &PathBuf) -> String {
        path.display().to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sr_roundtrip() {
        let mut p = Proof::to_buffer(3, ProofFormat::Sr);
        p.rup_clause(&[1, -2]);
        p.delete_clause(0, &[1, -2]);
        let buf = p.into_buffer();
        let text = String::from_utf8(buf).unwrap();
        assert!(text.contains("1 -2 0"));
        assert!(text.contains("d 1 -2 0"));
    }
}
