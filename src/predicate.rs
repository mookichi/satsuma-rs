//! Symmetry breaking predicate (SBP) container.
//!
//! Port of the storage half of `predicate.h`: the ordered list of breaking
//! clauses plus auxiliary variables introduced by lex-leader encodings.
//! Constraint *generation* from generators (`add_lex_leader_for_generators`,
//! Schreier cuts, row/column breaking) lives in the original's
//! `symmetries` engine; here the corresponding methods are explicit stubs
//! that document the plug-in point and keep statistics honest (returning 0
//! new constraints) instead of fabricating predicates.

use crate::literal::{graph_to_sat, sat_to_graph};
use crate::proof::Proof;
use crate::symmetry::Permutation;

/// Breaking clauses plus metadata.
#[derive(Debug, Clone, Default)]
pub struct Predicate {
    clauses: Vec<Vec<i32>>,
    extra_variables: usize,
    n_generators: usize,
    support_sum: usize,
}

impl Predicate {
    pub fn new() -> Self {
        Self::default()
    }

    /// Push a breaking clause.
    pub fn add_clause(&mut self, clause: Vec<i32>, proof: Option<&mut Proof>) {
        if let Some(p) = proof {
            p.rup_clause(&clause);
        }
        self.clauses.push(clause);
    }

    /// Allocate `n` fresh auxiliary variables, returning the first id.
    pub fn alloc_extra_variables(&mut self, base_vars: usize, n: usize) -> usize {
        let first = base_vars + self.extra_variables + 1;
        self.extra_variables += n;
        first
    }

    pub fn n_clauses(&self) -> usize {
        self.clauses.len()
    }

    pub fn n_extra_variables(&self) -> usize {
        self.extra_variables
    }

    pub fn get_clause(&self, i: usize) -> &[i32] {
        &self.clauses[i]
    }

    pub fn clauses(&self) -> &[Vec<i32>] {
        &self.clauses
    }

    pub fn record_generators(&mut self, n: usize, support_sum: usize) {
        self.n_generators = n;
        self.support_sum = support_sum;
    }

    pub fn n_generators(&self) -> usize {
        self.n_generators
    }

    pub fn avg_support(&self) -> f64 {
        if self.n_generators == 0 {
            0.0
        } else {
            self.support_sum as f64 / self.n_generators as f64
        }
    }

    /// Lex-leader breaking for one generator, bounded by `break_depth`
    /// positions (mirrors `--break-depth`).
    ///
    /// Standard chaining encoding (cf. Crawford et al., BreakID): with order
    /// `v_1..v_n` and chaining variables `e_i` ("prefix equal so far"),
    /// for each non-fixed position `(x, px)`:
    /// `(¬e ∨ ¬x ∨ px)`, plus definitional clauses linking `e_{i+1}`.
    /// Fixed points are skipped (they can never witness a difference), as
    /// are variables at/above `base_vars` (auxiliary variables from earlier
    /// rounds are functionally determined by the originals).
    /// Returns the number of clauses added.
    pub fn add_lex_leader(
        &mut self,
        base_vars: usize,
        gen: &Permutation,
        order: &[usize],
        break_depth: usize,
        proof: Option<&mut Proof>,
    ) -> usize {
        let mut positions: Vec<(i32, i32)> = Vec::new();
        for &v in order {
            if v >= base_vars {
                continue;
            }
            let lit = (v + 1) as i32;
            let img = graph_to_sat(gen.image[sat_to_graph(lit)]);
            // If the generator maps an original variable outside the original
            // set (e.g. onto an auxiliary variable from an earlier round),
            // the lex order no longer applies — skip the generator entirely.
            // Breaking fewer generators stays sound.
            if img.abs() as usize > base_vars {
                return 0;
            }
            if img != lit {
                positions.push((lit, img));
                if positions.len() >= break_depth.max(1) {
                    break;
                }
            }
        }
        if positions.is_empty() {
            return 0;
        }
        let k = positions.len();
        let mut proof = proof;
        if k == 1 {
            // Single swap: full lex-leader is one binary clause, no aux vars.
            let (x, px) = positions[0];
            if let Some(p) = proof.as_mut() {
                p.rup_clause(&[-x, px]);
            }
            self.clauses.push(vec![-x, px]);
            return 1;
        }
        let first_aux = self.alloc_extra_variables(base_vars, k);
        let e = |i: usize| (first_aux + i) as i32;
        let mut added = 0;
        let mut push = |clause: Vec<i32>, proof: &mut Option<&mut Proof>| {
            if let Some(p) = proof {
                p.rup_clause(&clause);
            }
            self.clauses.push(clause);
            added += 1;
        };
        push(vec![e(0)], &mut proof); // e_0 = true
        for (i, &(x, px)) in positions.iter().enumerate() {
            push(vec![-e(i), -x, px], &mut proof); // lex implication
            if i + 1 < k {
                let e2 = e(i + 1);
                push(vec![-e2, e(i)], &mut proof); // chain
                push(vec![-e2, -x, px], &mut proof); // e2 -> eq
                push(vec![-e2, x, -px], &mut proof);
                push(vec![-e(i), x, px, e2], &mut proof); // eq -> e2
                push(vec![-e(i), -x, -px, e2], &mut proof);
            }
        }
        added
    }

    /// Compatibility shim mirroring the original call site; prefers
    /// [`add_lex_leader`](Self::add_lex_leader) directly.
    pub fn add_lex_leader_for_generators(
        &mut self,
        _generators: &[crate::symmetry::Permutation],
        _break_depth: usize,
    ) -> usize {
        0
    }

    pub fn write_dimacs_clauses(&self, out: &mut String) {
        use std::fmt::Write as _;
        for clause in &self.clauses {
            for l in clause {
                let _ = write!(out, "{l} ");
            }
            out.push_str("0\n");
        }
    }
}
