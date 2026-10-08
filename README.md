# satsuma-rs

[日本語版はこちら](README.ja.md)

A pure-Rust port of [satsuma](https://github.com/markusa4/satsuma) (v1.4, C++) —
a static symmetry breaking preprocessor for SAT.

Given a DIMACS CNF formula, satsuma produces an equisatisfiable formula that
can be passed to any SAT solver. Two modes are supported:

- **`fix`**: iterative symmetry-based simplification/fixing (default).
- **`lex`**: lex-leader symmetry breaking constraints.

Dependency-free (no crates.io dependencies), edition 2021.

## Status

Functional port of the self-contained core plus a real,
pure-Rust symmetry engine:

- DIMACS parsing, watched-literal store with unit propagation, pure literals,
  subsumption, equivalent literals
- Deduplicating clause database with at-most-one (AMO) completion
- Model-graph automorphism search (individualization–refinement isomorphism
  search, every candidate verified exactly against the formula)
- Lex-leader breaking constraints (chaining encoding, generator inverses,
  support shortening via group-preserving products)
- Fixpoint iteration: breaking clauses are fed back and propagated
- Proof logging (SR / binary SR / VeriPB placeholders), statistics tracker
- CLI compatible with the original (`fix` / `lex`, `--file`, `--out-file`,
  `--proof-file`, `--break-depth`, `--opt`, `--preprocess-cnf`, …)

Known gaps vs. the C++ version: no Johnson/row/row-column structure
detection, no orbitopal/Schreier fixing (lex + propagation only), VeriPB
proof rules are placeholders, and detection is slower than dejavu
(time-budgeted, tunable). See [Porting notes](#porting-notes).

## Build

Requires a Rust toolchain (1.70+) and a C linker:

```sh
cargo build --release
```

## CLI usage

```sh
# Iterative fixing (reads file, writes to stdout by default)
./target/release/satsuma fix examples/php-015-014.cnf > out.cnf

# Lex-leader constraints
./target/release/satsuma lex formula.cnf --out-file out.cnf

# From stdin, with proof logging
cat formula.cnf | ./target/release/satsuma fix --proof-file proof.out > out.cnf
```

Common options:

| Flag | Effect |
|---|---|
| `--file`, `--out-file`, `--proof-file` | input / output / proof paths |
| `--break-depth N` | lex positions per generator (default 512) |
| `--preprocess-cnf` | unit + pure simplification in `lex` mode |
| `--schreier-cuts` / `--binary-clauses` | accepted for compatibility |
| `--add-reduced-as-unit` | keep models valid for the original formula |
| `--opt` / `--no-opt` | generator support shortening (default on) |
| `--sym-timeout MS` | detection budget per round (default 10000) |
| `--sym-pairs N` | max pair attempts per cell (default 512) |
| `--sym-nodes N` | max search nodes per pair (default 50000) |
| `--sr` / `--veripb` / `--bsr` | proof format (default SR) |
| `--silent` / `--verbose` | log control |

Example pipeline with a SAT solver:

```sh
satsuma fix php-015-014.cnf > php-015-014.break.cnf
cryptominisat5 php-015-014.break.cnf
```

## Library usage

```rust
use satsuma::{Mode, Preprocessor, PreprocessorConfig};

let dimacs = "p cnf 2 2\n1 2 0\n-1 -2 0\n";

// Fix mode with defaults.
let mut pp = Preprocessor::fix();
let out = pp.preprocess_str(dimacs).expect("valid dimacs");
println!("{}", out.dimacs); // `p cnf ...` + breaking clauses

// Custom configuration.
let config = PreprocessorConfig::new(Mode::Lex)
    .with_break_depth(64)
    .with_sym_time_budget_ms(2000);
let mut pp = Preprocessor::with_config(config);
let out = pp.preprocess_str(dimacs).unwrap();
assert!(!out.is_unsat());
```

`Output` carries `dimacs`, `n_variables`, `n_clauses`, `n_sbp_clauses`,
`n_extra_variables`, `n_generators`, `iterations`, `propagations`, and an
optional `proof_text`.

Custom symmetry backends can plug in behind the `SymmetryProvider` trait:

```rust
use satsuma::symmetry::{SymmetryGroup, SymmetryProvider};
use satsuma::Cnf;

struct MyBackend;
impl SymmetryProvider for MyBackend {
    fn detect(&mut self, formula: &Cnf) -> SymmetryGroup {
        // ... return verified generators + variable order ...
    }
}
```

## Module overview

| Module | Contents |
|---|---|
| `parser` | DIMACS CNF parsing (`parse_dimacs_str`, file/stdin) |
| `cnf2wl` | Watched-literal store: propagation, pure, subsumption, equivalents |
| `cnf` | Deduplicating clause database + AMO completion |
| `graph` | Colored model graph + canonical color refinement (WL-1) |
| `automorphism` | Iso-search, exact verification, `GraphAutomorphismProvider` |
| `predicate` | Symmetry breaking predicate (lex-leader encoding) |
| `preprocessor` | `PreprocessorConfig` + pipeline (`fix` / `lex`, iteration) |
| `symmetry` | `SymmetryProvider` trait, permutations, orbit partitions |
| `proof` | Proof logging (SR / binary SR / VeriPB) |
| `tracker` | Run statistics |
| `literal` | SAT literal ↔ graph vertex mappings |

## Verification

- `cargo test`: 21 unit/integration tests + doctests.
- Differential testing against the C++ build (see `difftest.py` workflow):
  validity of outputs plus equisatisfiability (DPLL-checked) over hundreds
  of random, planted-symmetry, pigeonhole, unit-heavy, large, and edge-case
  formulas in both modes — thousands of runs, zero violations.

## Porting notes

- Symmetry breaking covers a (verified) subgroup; partial detection weakens
  reduction only, never soundness.
- Assigned literals are colored distinctly in the model graph, so detection
  only returns symmetries stabilizing the current partial assignment
  (required for sound breaking after simplification — same approach as
  BreakID).
- Detection effort is wall-clock budgeted, so generator sets (and hence
  reduction strength) can vary between runs; outputs are always equisatisfiable.
- Proof logging for lex-leader clauses is best-effort (rule-level VeriPB
  logging is future work, as in upstream where it is experimental).

## Publications

The upstream design is described in:

- “Satsuma: Structure-based Symmetry Breaking in SAT” (SAT ’24) —
  Markus Anders, Sofia Brenner, Gaurav Rattan
- “Algorithms Transcending the SAT-Symmetry Interface” (SAT ’23) —
  Markus Anders, Mate Soos, Pascal Schweitzer
- “SAT Preprocessors and Symmetry” (SAT ’22) — Markus Anders

## License

MIT, matching upstream. Upstream copyright: Markus Anders (see `LICENSE`
of markusa4/satsuma); the `tsl` robin-hood hashing headers it replaces are
by Thibaut Goetghebuer-Planchon.
