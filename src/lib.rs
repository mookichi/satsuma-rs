//! `satsuma` — static symmetry breaking preprocessor for SAT.
//!
//! Pure-Rust port of <https://github.com/markusa4/satsuma> (v1.4, C++).
//!
//! Given a DIMACS CNF formula, satsuma produces an equisatisfiable formula
//! that can be passed to any SAT solver. Two modes are supported:
//!
//! * **fix**: iterative symmetry-based fixing / simplification.
//! * **lex**: lex-leader symmetry breaking constraints.
//!
//! # Porting notes
//!
//! The self-contained parts of the original are faithfully ported:
//! DIMACS parsing ([`parser`]), the watched-literal store with unit
//! propagation ([`CnfWl`](cnf2wl::CnfWl)), the deduplicating clause database
//! ([`Cnf`](cnf::Cnf)), proof logging ([`proof`]) and statistics
//! ([`tracker`]).
//!
//! The symmetry engine is pure Rust: the formula becomes a colored model
//! graph ([`graph`]), automorphisms are found by individualization-refinement
//! isomorphism search ([`automorphism`], every candidate verified exactly
//! against the formula), and a subgroup is broken with lex-leader
//! constraints ([`predicate`]). Because breaking any subgroup preserves
//! satisfiability both ways, partial detection only weakens reduction —
//! never soundness. Assigned literals are colored distinctly so detection
//! only returns symmetries stabilizing the current partial assignment
//! (required for sound breaking after simplification). Search effort is
//! bounded by time/pair/node budgets
//! ([`automorphism::SearchLimits`], tunable via `--sym-timeout`,
//! `--sym-pairs`, `--sym-nodes`); custom backends can still plug in behind
//! the [`symmetry::SymmetryProvider`] trait.
//!
//! # Example
//!
//! ```rust
//! use satsuma::{Preprocessor, PreprocessorConfig, Mode};
//!
//! let dimacs = "p cnf 1 2\n1 0\n-1 0\n";
//! let config = PreprocessorConfig::new(Mode::Fix);
//! let out = Preprocessor::with_config(config)
//!     .preprocess_str(dimacs)
//!     .expect("valid dimacs");
//! assert!(out.is_unsat()); // empty clause derived
//! ```

pub mod automorphism;
pub mod cnf;
pub mod cnf2wl;
pub mod graph;
pub mod literal;
pub mod parser;
pub mod predicate;
pub mod preprocessor;
pub mod proof;
pub mod symmetry;
pub mod tracker;

pub use cnf::Cnf;
pub use cnf2wl::CnfWl;
pub use preprocessor::{Mode, Output, Preprocessor, PreprocessorConfig};

/// Crate version, mirrors `SATSUMA_VERSION_MAJOR.MINOR` of the original.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
/// Major version of the upstream this port tracks.
pub const UPSTREAM_VERSION_MAJOR: u32 = 1;
/// Minor version of the upstream this port tracks.
pub const UPSTREAM_VERSION_MINOR: u32 = 4;
