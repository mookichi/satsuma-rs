//! `satsuma` CLI: `satsuma fix|lex [<dimacs>] [options]`.
//!
//! Mirrors the argument surface of the original `satsuma.cpp`
//! (`commandline_mode`), including `--file`, `--out-file`, `--proof-file`,
//! `--break-depth`, `--opt*`, `--preprocess-cnf`, `--schreier-cuts`,
//! `--add-reduced-as-unit`, `--silent/--verbose`, and `--sr/--veripb/--bsr`.
//! Options that tune the not-yet-ported dejavu engine are accepted for
//! script compatibility and noted as no-ops in verbose output.

use satsuma::proof::{Proof, ProofFormat};
use satsuma::{Mode, Preprocessor, PreprocessorConfig};
use std::io::{self, Read};
use std::path::PathBuf;

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn print_help() {
    eprintln!("Satsuma has two modes:\n");
    eprintln!("     satsuma fix [<dimacs>] [<options>] (iterative fixing)");
    eprintln!("     satsuma lex [<dimacs>] [<options>] (lex constraints)\n");
    eprintln!("'fix' simplifies the CNF using symmetry");
    eprintln!("'lex' computes lex-leader symmetry breaking constraints\n");
    eprintln!("Options:\n");
    eprintln!("   --file [FILE]           Input file in CNF format");
    eprintln!("   --out-file [FILE]       Output file in CNF format");
    eprintln!("   --proof-file [FILE]     Proof file in SR or VeriPB format");
    eprintln!();
    eprintln!("   --break-depth [N]       Limits generic breaking constraints to depth n (lex)");
    eprintln!("   --preprocess-cnf        Preprocess before symmetry breaking (lex)");
    eprintln!("   --schreier-cuts         Use the Schreier cut heuristic (lex)");
    eprintln!("   --opt                   Optimize generators");
    eprintln!("   --opt-passes [N]        Passes used in support optimization");
    eprintln!("   --opt-conjugations [N]  Limit for conjugates added from generators");
    eprintln!("   --opt-random [N]        Maximum number of random generators added");
    eprintln!("   --opt-reopt             Optimizes generators twice");
    eprintln!("   --add-reduced-as-unit   Keep satisfying assignments valid for the original formula");
    eprintln!("   --sym-timeout [MS]    Symmetry detection budget per round (default 10000)");
    eprintln!("   --sym-pairs [N]       Max automorphism pair attempts per cell (default 512)");
    eprintln!("   --sym-nodes [N]       Max search nodes per pair attempt (default 50000)");
    eprintln!("   --no-opt              Disable generator support shortening");
    eprintln!("   --sr / --veripb / --bsr Proof format (default: SR)");
    eprintln!("   --silent / --verbose    Suppress / enable log output");
}

fn banner(mode: Mode) {
    eprintln!("c ┌────────────────────────────────────────────────────────────────┐");
    eprintln!("c │      satsuma-rs -- a symmetry preprocessor for SAT          │");
    eprintln!("c │      satsuma_version={VERSION} (rust port of satsuma 1.4)      │");
    eprintln!(
        "c │      mode={}                                           │",
        match mode {
            Mode::Fix => "fix",
            Mode::Lex => "lex",
        }
    );
    eprintln!("c └────────────────────────────────────────────────────────────────┘");
}

fn main() {
    let argv: Vec<String> = std::env::args().collect();
    if argv.len() < 2 {
        eprintln!("Satsuma has two modes:\n");
        eprintln!("     satsuma fix [<dimacs>] [<options>] (iterative fixing)");
        eprintln!("     satsuma lex [<dimacs>] [<options>] (lex constraints)");
        eprintln!("\nConsult satsuma --help for more options.");
        std::process::exit(0);
    }
    if argv[1] == "--help" || argv[1] == "-h" {
        print_help();
        return;
    }
    if argv[1] == "--version" || argv[1] == "-V" {
        eprintln!("{VERSION}");
        return;
    }

    let mode = match argv[1].as_str() {
        "fix" => Mode::Fix,
        "lex" => Mode::Lex,
        other => {
            eprintln!("Unknown mode '{other}'. Expected 'fix' or 'lex'.");
            std::process::exit(1);
        }
    };
    let mut config = PreprocessorConfig::new(mode);

    let mut input_file: Option<String> = None;
    let mut out_file: Option<PathBuf> = None;
    let mut proof_file: Option<PathBuf> = None;
    let mut silent = false;
    let mut verbose = false;

    let mut i = 2;
    while i < argv.len() {
        let normalized = argv[i].replace('-', "_").to_uppercase();
        match normalized.as_str() {
            "__HELP" | "_H" => {
                print_help();
                return;
            }
            "__VERSION" | "_V" => {
                eprintln!("{VERSION}");
                return;
            }
            "__FILE" | "_F" => {
                i += 1;
                if i >= argv.len() {
                    eprintln!("--file option requires one argument.");
                    std::process::exit(1);
                }
                input_file = Some(argv[i].clone());
            }
            "__OUT_FILE" | "_O" => {
                i += 1;
                if i >= argv.len() {
                    eprintln!("--out-file option requires one argument.");
                    std::process::exit(1);
                }
                out_file = Some(PathBuf::from(&argv[i]));
            }
            "__PROOF_FILE" => {
                i += 1;
                if i >= argv.len() {
                    eprintln!("--proof-file option requires one argument.");
                    std::process::exit(1);
                }
                if proof_file.is_some() {
                    eprintln!("Only 1 proof file possible.");
                    std::process::exit(1);
                }
                proof_file = Some(PathBuf::from(&argv[i]));
            }
            "__BREAK_DEPTH" => {
                i += 1;
                match argv.get(i).and_then(|s| s.parse::<usize>().ok()) {
                    Some(d) => config = config.with_break_depth(d),
                    None => {
                        eprintln!("--break-depth option requires one argument.");
                        std::process::exit(1);
                    }
                }
            }
            "__PREPROCESS_CNF" => {
                config = config.with_unit(true).with_pure(true);
            }
            "__PREPROCESS_CNF_UNIT" => config = config.with_unit(true),
            "__PREPROCESS_CNF_PURE" => config = config.with_pure(true),
            "__PREPROCESS_CNF_SUBSUME" => config = config.with_subsume(true),
            "__ADD_REDUCED_AS_UNIT" => config = config.with_add_reduced_as_unit(true),
            "__BINARY_CLAUSES" | "__SCHREIER_CUTS" => {
                config = config.with_binary_clauses(true);
            }
            "__ITERATE" | "__FIX_AND_CUT" => config = config.with_iterate(true),
            "__SILENT" => silent = true,
            "__VERBOSE" => verbose = true,
            "__SR" => config = config.with_proof_format(ProofFormat::Sr),
            "__VERIPB" => config = config.with_proof_format(ProofFormat::VeriPb),
            "__BSR" => config = config.with_proof_format(ProofFormat::BinarySr),
            "__OPT" => {
                config.optimize_generators = true;
            }
            "__NO_OPT" => {
                config.optimize_generators = false;
            }
            "__SYM_TIMEOUT" => {
                i += 1;
                match argv.get(i).and_then(|s| s.parse::<u64>().ok()) {
                    Some(ms) => config.sym_time_budget_ms = ms,
                    None => {
                        eprintln!("--sym-timeout option requires one argument.");
                        std::process::exit(1);
                    }
                }
            }
            "__SYM_PAIRS" => {
                i += 1;
                match argv.get(i).and_then(|s| s.parse::<usize>().ok()) {
                    Some(n) => config.sym_max_pairs = n,
                    None => {
                        eprintln!("--sym-pairs option requires one argument.");
                        std::process::exit(1);
                    }
                }
            }
            "__SYM_NODES" => {
                i += 1;
                match argv.get(i).and_then(|s| s.parse::<u64>().ok()) {
                    Some(n) => config.sym_max_nodes = n,
                    None => {
                        eprintln!("--sym-nodes option requires one argument.");
                        std::process::exit(1);
                    }
                }
            }
            // Accepted for compatibility; engine not yet ported.
            "__OPT_REOPT" | "__DEJAVU_PRINT" | "__DEJAVU_PREFER_DFS"
            | "__NO_LIMITS" | "__PREPROCESS_CNF_EQ" | "__HYPERGRAPH_MACROS"
            | "__NO_HYPERGRAPH_MACROS" | "__ORBITOPAL_FIXING" | "__SCHREIER_FIXING"
            | "__NEGATION_FIXING" | "__FIXING" | "__REORDER" | "__CLIQUER"
            | "__STRUCT_ONLY" | "__USE_FIRST_LIT" | "__CNF" | "__KNF" | "__PB"
            | "__NO_PROFILE" | "__OPT_PASSES" | "__OPT_CONJUGATIONS" | "__OPT_RANDOM"
            | "__COMPONENT_LIMIT" | "__ROW_ORBIT_LIMIT" | "__ROW_COLUMN_ORBIT_LIMIT"
            | "__JOHNSON_ORBIT_LIMIT" | "__SPARSE_MODEL_LIMIT" | "__DENSE_MODEL_LIMIT"
            | "__FULL_SKIP_LIMIT" | "__ORDER_MODEL_LIMIT" | "__PROOF_DENSE_CROSSOVER"
            | "__PROOF_SPARSE_RUP" | "__OUTPUT_GRAPH_FILE" | "__INPUT_GRAPH_FILE" | "_G"
            | "_M" => {
                // Skip the value of options that take an argument.
                const WITH_ARG: &[&str] = &[
                    "__OPT_PASSES",
                    "__OPT_CONJUGATIONS",
                    "__OPT_RANDOM",
                    "__COMPONENT_LIMIT",
                    "__ROW_ORBIT_LIMIT",
                    "__ROW_COLUMN_ORBIT_LIMIT",
                    "__JOHNSON_ORBIT_LIMIT",
                    "__SPARSE_MODEL_LIMIT",
                    "__DENSE_MODEL_LIMIT",
                    "__FULL_SKIP_LIMIT",
                    "__ORDER_MODEL_LIMIT",
                    "__PROOF_DENSE_CROSSOVER",
                    "__OUTPUT_GRAPH_FILE",
                    "__INPUT_GRAPH_FILE",
                    "_G",
                    "_M",
                ];
                if WITH_ARG.contains(&normalized.as_str()) {
                    i += 1;
                }
                if verbose {
                    eprintln!("c note: '{}' accepted for compatibility (no-op in Rust port)", argv[i.min(argv.len()-1)]);
                }
            }
            _ if argv[i].starts_with('-') => {
                eprintln!("Invalid commandline option '{}'.", argv[i]);
                std::process::exit(1);
            }
            _ => {
                if input_file.is_none() {
                    input_file = Some(argv[i].clone());
                } else {
                    eprintln!("Extraneous file '{}'. Only 1 file required.", argv[i]);
                    std::process::exit(1);
                }
            }
        }
        i += 1;
    }

    if !silent {
        banner(mode);
        if input_file.is_none() {
            eprintln!("c no file specified, reading from stdin, (use --help for options)");
        }
    }

    // Read input.
    let text = match &input_file {
        Some(path) => std::fs::read_to_string(path).unwrap_or_else(|e| {
            eprintln!("file '{path}' does not exist ({e})");
            std::process::exit(1);
        }),
        None => {
            let mut buf = String::new();
            io::stdin().read_to_string(&mut buf).unwrap_or_else(|e| {
                eprintln!("could not read stdin: {e}");
                std::process::exit(1);
            });
            buf
        }
    };

    let mut formula = match satsuma::parser::parse_dimacs_str(&text) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("c \nc {e}");
            std::process::exit(1);
        }
    };
    if !silent {
        eprintln!(
            "c parse '{}', expecting cnf",
            input_file.as_deref().unwrap_or("<stdin>")
        );
        eprintln!(
            "c\t [cnf: #vars {} #cls {}]",
            formula.n_variables(),
            formula.n_clauses()
        );
    }

    let mut pp = Preprocessor::with_config(config.clone());
    if let Some(path) = &proof_file {
        match Proof::to_file(path, formula.n_variables(), config.proof_format) {
            Ok(p) => pp = pp.with_proof(p),
            Err(e) => {
                eprintln!("c \nc could not open proof file '{}': {e}", path.display());
                std::process::exit(1);
            }
        }
        if !silent {
            eprintln!("c output proof to '{}'", path.display());
        }
    }

    let out = pp.preprocess_wl(&mut formula);
    if !silent {
        eprintln!("c preprocessing finished");
        eprintln!(
            "c [out: #vars {} #cls {} (+{} sbp) gens={}] iterations={} propagations={}",
            out.n_variables,
            out.n_clauses,
            out.n_sbp_clauses,
            out.n_generators,
            out.iterations,
            out.propagations
        );
    }

    if let Some(path) = out_file {
        std::fs::write(&path, &out.dimacs).unwrap_or_else(|e| {
            eprintln!("unable to open output file '{}': {e}", path.display());
            std::process::exit(1);
        });
        if !silent {
            eprintln!("c wrote output to '{}'", path.display());
        }
    } else {
        print!("{}", out.dimacs);
    }
}
