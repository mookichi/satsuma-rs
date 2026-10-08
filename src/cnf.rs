//! Deduplicating clause database.
//!
//! Port of `cnf.h`: a hash table of clauses (split by size for the small
//! cases) guarantees no duplicate clause is stored. Clauses keep their
//! original literal order; a sorted canonical copy is used for hashing,
//! exactly like `keep_original_order = true` in the original.

use crate::literal::sat_to_graph;
use std::collections::{HashMap, HashSet};

/// Deduplicated CNF, mirroring class `cnf`.
#[derive(Debug, Clone, Default)]
pub struct Cnf {
    clause_db_arbitrary: HashSet<Vec<i32>>,
    clause_db_size2: HashSet<(i32, i32)>,
    clause_db_size3: HashSet<(i32, i32, i32)>,

    clauses_pt: Vec<(usize, usize)>,
    clauses: Vec<i32>,

    /// (positive, negative) occurrence counts per variable.
    var_counts: Vec<(usize, usize)>,
    /// Clause ids using each variable.
    var_used: Vec<Vec<usize>>,

    n_variables: usize,
    removed_duplicate_clauses: usize,
    added_amo_clauses: usize,
    equivalent_literal_subst: usize,
    taut_removed: usize,
    min_clause_size: usize,

    pub unique_literal_clauses: Vec<usize>,
    pub binary_clauses: Vec<usize>,

    /// Literals assigned TRUE under the current partial assignment
    /// (indexed by graph literal). Symmetries must stabilize this set
    /// (and its negation) setwise — otherwise breaking them is unsound.
    /// Filled by [`read_from_wl`](Self::read_from_wl).
    pub unit_true: Vec<bool>,
}

impl Cnf {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reserve(&mut self, n: usize, m: usize) {
        self.n_variables = n;
        self.clauses_pt.reserve(m);
        self.clauses.reserve(3 * m.max(1));
        self.var_used.resize(n, Vec::new());
        self.var_counts.resize(n, (0, 0));
        self.clause_db_arbitrary.reserve(m);
        self.min_clause_size = usize::MAX;
        self.unit_true = vec![false; 2 * n];
    }

    fn canonical(mut clause: Vec<i32>) -> Vec<i32> {
        clause.sort_unstable();
        clause.dedup();
        clause
    }

    fn contains_canonical(&self, canon: &[i32]) -> bool {
        match canon.len() {
            2 => self.clause_db_size2.contains(&(canon[0], canon[1])),
            3 => self
                .clause_db_size3
                .contains(&(canon[0], canon[1], canon[2])),
            _ => self.clause_db_arbitrary.contains(canon),
        }
    }

    fn insert_canonical(&mut self, canon: &[i32]) -> bool {
        match canon.len() {
            2 => self.clause_db_size2.insert((canon[0], canon[1])),
            3 => self
                .clause_db_size3
                .insert((canon[0], canon[1], canon[2])),
            _ => self.clause_db_arbitrary.insert(canon.to_vec()),
        }
    }

    /// Add a clause. Returns `true` iff the clause was actually stored.
    /// Tautologies and duplicates are rejected (and counted).
    pub fn add_clause(&mut self, clause: &[i32]) -> bool {
        // Tautology / duplicate-literal check via graph-literal set.
        let mut seen: HashSet<usize> = HashSet::with_capacity(clause.len() * 2);
        let mut dedup: Vec<i32> = Vec::with_capacity(clause.len());
        for &l in clause {
            let g = sat_to_graph(l);
            let gn = sat_to_graph(-l);
            if seen.contains(&g) {
                continue;
            }
            if seen.contains(&gn) {
                self.taut_removed += 1;
                return false;
            }
            seen.insert(g);
            dedup.push(l);
        }
        let canon = Self::canonical(dedup.clone());
        if self.contains_canonical(&canon) {
            self.removed_duplicate_clauses += 1;
            return false;
        }
        self.insert_canonical(&canon);
        if canon.len() < self.min_clause_size {
            self.min_clause_size = canon.len();
        }
        let start = self.clauses.len();
        self.clauses.extend_from_slice(&dedup);
        let end = self.clauses.len();
        let id = self.clauses_pt.len();
        self.clauses_pt.push((start, end));
        for &l in &dedup {
            let v = (l.abs() - 1) as usize;
            if l > 0 {
                self.var_counts[v].0 += 1;
            } else {
                self.var_counts[v].1 += 1;
            }
            self.var_used[v].push(id);
        }
        true
    }

    /// Import from a [`crate::CnfWl`], applying assignments and
    /// equivalent-literal representatives. Mirrors `read_from_cnf2wl`
    /// (without proof logging here; the preprocessor logs instead).
    pub fn read_from_wl(
        &mut self,
        formula: &mut crate::CnfWl,
        removed_clause_ids: &mut Vec<Vec<i32>>,
    ) {
        let end = formula.n_clauses();
        self.read_from_wl_range(formula, removed_clause_ids, end);
    }

    /// Same as [`read_from_wl`](Self::read_from_wl) but only imports clauses
    /// `[0, end)` — used to exclude appended symmetry-breaking clauses from
    /// symmetry detection and from duplication in the output.
    pub fn read_from_wl_range(
        &mut self,
        formula: &mut crate::CnfWl,
        removed_clause_ids: &mut Vec<Vec<i32>>,
        end: usize,
    ) {
        let end = end.min(formula.n_clauses());
        self.reserve(formula.n_variables(), formula.n_clauses());
        // Record the current partial assignment: symmetries must stabilize
        // assigned literals setwise for breaking to stay sound.
        for g in 0..2 * formula.n_variables() {
            if formula.assigned(crate::literal::graph_to_sat(g)) == 1 {
                self.unit_true[g] = true;
            }
        }
        for c in 0..end {
            if formula.is_satisfied(c) {
                continue;
            }
            let mut next: Vec<i32> = Vec::new();
            let mut satisfied = false;
            for j in 0..formula.clause_size(c) {
                let orig = formula.literal_at_clause_pos(c, j);
                let repr = formula.representative(orig);
                if orig != repr {
                    self.equivalent_literal_subst += 1;
                }
                match formula.assigned(repr) {
                    1 => {
                        satisfied = true;
                        break;
                    }
                    0 => next.push(repr),
                    _ => {}
                }
            }
            if satisfied {
                continue;
            }
            if !self.add_clause(&next) {
                let (s, e) = (0, 0);
                let _ = (s, e);
                removed_clause_ids.push(next);
            }
        }
    }

    /// Complete unique-literal clauses with at-most-one (AMO) constraints.
    /// Returns the number of unique-literal clauses. Mirrors `ulc_add_amo`.
    pub fn ulc_add_amo(&mut self) -> usize {
        self.unique_literal_clauses.clear();
        let n = self.n_clauses();
        for i in 0..n {
            let clause = self.clause(i).to_vec();
            if clause.iter().all(|&l| self.literal_occurrences(l) == 1) {
                if !self.is_amo_clause(&clause) {
                    self.insert_amo(&clause);
                }
                self.unique_literal_clauses.push(i);
            }
        }
        self.unique_literal_clauses.len()
    }

    pub fn compute_binary(&mut self) -> usize {
        self.binary_clauses.clear();
        for i in 0..self.n_clauses() {
            if self.clause_size(i) == 2 {
                self.binary_clauses.push(i);
            }
        }
        self.binary_clauses.len()
    }

    pub fn is_clause(&self, clause: &[i32]) -> bool {
        self.contains_canonical(&Self::canonical(clause.to_vec()))
    }

    fn is_amo_clause(&self, row: &[i32]) -> bool {
        if self.min_clause_size > 2 {
            return false;
        }
        for (i, &l1) in row.iter().enumerate() {
            for &l2 in &row[i + 1..] {
                if !self.is_clause(&[-l1, -l2]) {
                    return false;
                }
            }
        }
        true
    }

    fn insert_amo(&mut self, row: &[i32]) {
        for (i, &l1) in row.iter().enumerate() {
            for &l2 in &row[i + 1..] {
                let pair = vec![-l1, -l2];
                if !self.is_clause(&pair) {
                    self.added_amo_clauses += 1;
                    self.add_clause(&pair);
                }
            }
        }
    }

    pub fn literal_occurrences(&self, lit: i32) -> usize {
        let v = (lit.abs() - 1) as usize;
        if lit > 0 {
            self.var_counts[v].0
        } else {
            self.var_counts[v].1
        }
    }

    pub fn clause(&self, c: usize) -> &[i32] {
        let (s, e) = self.clauses_pt[c];
        &self.clauses[s..e]
    }

    pub fn clause_size(&self, c: usize) -> usize {
        let (s, e) = self.clauses_pt[c];
        e - s
    }

    pub fn n_clauses(&self) -> usize {
        self.clauses_pt.len()
    }

    pub fn n_variables(&self) -> usize {
        self.n_variables
    }

    pub fn n_len(&self) -> usize {
        self.clauses.len()
    }

    pub fn n_duplicate_clauses_removed(&self) -> usize {
        self.removed_duplicate_clauses
    }

    pub fn n_amo_clauses_added(&self) -> usize {
        self.added_amo_clauses
    }

    pub fn n_eq_literal_subst(&self) -> usize {
        self.equivalent_literal_subst
    }

    /// Variable -> clauses map, for symmetry analysis.
    pub fn occurrence_lists(&self) -> &Vec<Vec<usize>> {
        &self.var_used
    }

    pub fn clauses_iter(&self) -> impl Iterator<Item = &[i32]> {
        (0..self.n_clauses()).map(|c| self.clause(c))
    }

    /// Append DIMACS clause lines (`l1 l2 ... 0`) to `out`.
    pub fn write_dimacs_clauses(&self, out: &mut String) {
        use std::fmt::Write as _;
        for c in 0..self.n_clauses() {
            for l in self.clause(c) {
                let _ = write!(out, "{l} ");
            }
            out.push_str("0\n");
        }
    }

    /// Occurrence statistics: (variable id, #clauses using it).
    pub fn variable_occurrences(&self) -> HashMap<usize, usize> {
        self.var_used
            .iter()
            .enumerate()
            .map(|(v, list)| (v, list.len()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dedup_and_taut() {
        let mut db = Cnf::new();
        db.reserve(2, 4);
        assert!(db.add_clause(&[1, 2]));
        assert!(!db.add_clause(&[2, 1])); // duplicate
        assert!(!db.add_clause(&[1, -1])); // tautology
        assert_eq!(db.n_clauses(), 1);
        assert_eq!(db.n_duplicate_clauses_removed(), 1);
    }

    #[test]
    fn amo_completion() {
        let mut db = Cnf::new();
        db.reserve(5, 4);
        db.add_clause(&[1, 2, 3]);
        db.add_clause(&[4, 5]); // keep min_clause_size small
        let n = db.ulc_add_amo();
        assert!(n >= 1);
        assert!(db.is_clause(&[-1, -2]));
    }
}
