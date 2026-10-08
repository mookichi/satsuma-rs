//! Watched-literal CNF store with unit propagation.
//!
//! Faithful port of `cnf2wl.h`: clauses are stored contiguously, two watches
//! per clause drive propagation, and helper routines implement pure-literal
//! detection, subsumption marking and equivalent-literal substitution via
//! union-find (the original uses dejavu's `orbit` structure for the latter;
//! semantics are identical).

use crate::literal::{graph_to_sat, sat_to_graph};

/// Union-find used for equivalent literals (`x <-> y` discovered from
/// binary clause pairs).
#[derive(Debug, Clone, Default)]
struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn init(&mut self, n: usize) {
        self.parent = (0..n).collect();
    }

    fn find(&mut self, x: usize) -> usize {
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        // Path compression.
        let mut cur = x;
        while self.parent[cur] != root {
            let next = self.parent[cur];
            self.parent[cur] = root;
            cur = next;
        }
        root
    }

    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent[ra] = rb;
        }
    }

    fn grow(&mut self, n: usize) {
        let cur = self.parent.len();
        if n > cur {
            self.parent.extend(cur..n);
        }
    }
}

/// CNF formula with watched literals, mirroring `cnf2wl`.
#[derive(Debug, Clone, Default)]
pub struct CnfWl {
    /// Clause spans into `clauses`.
    clauses_pt: Vec<(usize, usize)>,
    /// Watch positions (indices into `clauses`) per clause.
    clauses_watches: Vec<(usize, usize)>,
    /// All literals, concatenated.
    clauses: Vec<i32>,
    /// Clauses containing each graph literal.
    literal_used_list: Vec<Vec<usize>>,
    /// Clauses watched by each variable (indexed by `abs(lit)`).
    variable_watches: Vec<Vec<usize>>,

    /// Assignment indexed by graph literal: 1 true, -1 false, 0 unassigned.
    assignment: Vec<i8>,
    n_variables: usize,

    units_applied: usize,
    redundant_removed: usize,
    literals_removed: usize,
    subsumptions_found: usize,
    conflict: bool,

    in_units: Vec<bool>,
    units: Vec<i32>,

    equivalent: UnionFind,

    clause_satisfied: Vec<bool>,
    found_literal: Vec<bool>,
    test_redundant: Vec<bool>,
    test_for_subsumption: Vec<bool>,
}

impl CnfWl {
    pub fn new() -> Self {
        Self::default()
    }

    /// Reserve space for `n` variables and `m` clauses.
    pub fn reserve(&mut self, n: usize, m: usize) {
        self.n_variables = n;
        self.clauses_pt.reserve(m);
        self.clauses.reserve(4 * m.max(1));
        self.clauses_watches.reserve(m);
        self.literal_used_list.resize(2 * n, Vec::new());
        // Index 0 unused; variable v uses entry v.
        self.variable_watches.resize(n + 1, Vec::new());
        self.assignment = vec![0; 2 * n];
        self.found_literal = vec![false; 2 * n];
        self.test_redundant = vec![false; 2 * n];
        self.test_for_subsumption = vec![false; m.max(1)];
        self.clause_satisfied = vec![false; m.max(1)];
        self.in_units = vec![false; 2 * n];
        self.equivalent.init(2 * n);
    }

    fn ensure_clause_capacity(&mut self, clause_number: usize) {
        if clause_number >= self.clause_satisfied.len() {
            let grown = (clause_number + 1).next_power_of_two();
            self.clause_satisfied.resize(grown, false);
            self.test_for_subsumption.resize(grown, false);
        }
        if clause_number >= self.clauses_watches.len() {
            self.clauses_watches.resize(clause_number + 1, (0, 0));
        }
    }

    /// Grow the variable domain by `additional` variables (for auxiliary
    /// variables introduced by symmetry breaking). Existing clauses and
    /// assignments are preserved.
    pub fn extend_variables(&mut self, additional: usize) {
        if additional == 0 {
            return;
        }
        let old_n = self.n_variables;
        let new_n = old_n + additional;
        self.n_variables = new_n;
        self.literal_used_list.resize(2 * new_n, Vec::new());
        self.variable_watches.resize(new_n + 1, Vec::new());
        self.assignment.resize(2 * new_n, 0);
        self.found_literal.resize(2 * new_n, false);
        self.test_redundant.resize(2 * new_n, false);
        self.in_units.resize(2 * new_n, false);
        self.equivalent.grow(2 * new_n);
    }

    /// Add a clause, removing duplicate literals and dropping tautologies.
    /// Mirrors `cnf2wl::add_clause`.
    pub fn add_clause(&mut self, clause: &[i32]) {
        for b in self.test_redundant.iter_mut() {
            *b = false;
        }
        let clause_pos = self.clauses.len();
        let mut pushed = 0usize;
        for &l in clause {
            debug_assert!(l != 0);
            let g = sat_to_graph(l);
            let gn = sat_to_graph(-l);
            if self.test_redundant[g] {
                self.literals_removed += 1;
                continue;
            }
            if self.test_redundant[gn] {
                // Tautology: roll back.
                self.redundant_removed += 1;
                self.clauses.truncate(clause_pos);
                return;
            }
            self.clauses.push(l);
            pushed += 1;
            self.test_redundant[g] = true;
        }
        let _ = pushed;
        let clause_number = self.clauses_pt.len();
        self.ensure_clause_capacity(clause_number);
        self.clauses_pt.push((clause_pos, self.clauses.len()));
        for &l in &self.clauses[clause_pos..self.clauses.len()] {
            self.literal_used_list[sat_to_graph(l)].push(clause_number);
        }
        self.initialize_watches(clause_number);
    }

    // -- assignment / propagation -----------------------------------------

    /// Current assignment of a literal: 1 true, -1 false, 0 unassigned.
    pub fn assigned(&self, lit: i32) -> i8 {
        self.assignment[sat_to_graph(lit)]
    }

    /// Representative of a literal under equivalent-literal substitution.
    pub fn representative(&mut self, lit: i32) -> i32 {
        let g = sat_to_graph(lit);
        let r = self.equivalent.find(g);
        graph_to_sat(r)
    }

    fn queue_unit(&mut self, lit: i32) {
        let g = sat_to_graph(lit);
        if !self.in_units[g] {
            self.in_units[g] = true;
            self.units.push(lit);
        }
    }

    /// Assign a literal and update watches / satisfied flags.
    pub fn assign_literal(&mut self, lit: i32) {
        if self.conflict {
            return;
        }
        let g = sat_to_graph(lit);
        let gn = sat_to_graph(-lit);
        if self.assignment[g] != 0 {
            if self.assignment[g] == -1 {
                self.conflict = true;
            }
            return;
        }
        self.assignment[g] = 1;
        self.assignment[gn] = -1;
        for &c in self.literal_used_list[g].clone().iter() {
            if c < self.clause_satisfied.len() {
                self.clause_satisfied[c] = true;
            }
        }
        let var = lit.abs() as usize;
        // Drain ALL watches on this variable. update_watches always removes
        // the processed entry (relocating the watch as needed), so this
        // terminates. (Breaking early here starves propagation.)
        while let Some(&clause_number) = self.variable_watches[var].last() {
            let pos = self.variable_watches[var].len() - 1;
            self.update_watches(clause_number, var, pos);
            if self.conflict {
                break;
            }
        }
    }

    /// Propagate all queued units. Returns the number of propagations.
    /// Mirrors `cnf2wl::propagate`.
    pub fn propagate(&mut self) -> usize {
        if self.conflict {
            return 0;
        }
        let mut propagations = 0;
        while let Some(lit) = self.units.pop() {
            self.in_units[sat_to_graph(lit)] = false;
            if self.conflict {
                break;
            }
            if self.assigned(lit) == -1 {
                self.conflict = true;
                break;
            }
            if self.assigned(lit) == 0 {
                self.assign_literal(lit);
                propagations += 1;
                self.units_applied += 1;
            }
        }
        propagations
    }

    fn add_watch(&mut self, lit: i32, clause: usize) {
        let var = lit.abs() as usize;
        if var < self.variable_watches.len() {
            self.variable_watches[var].push(clause);
        }
    }

    fn remove_watch(&mut self, var: usize, pos: usize) {
        let watches = &mut self.variable_watches[var];
        let last = watches.len() - 1;
        watches.swap(pos, last);
        watches.pop();
    }

    fn initialize_watches(&mut self, clause_number: usize) {
        let size = self.clause_size(clause_number);
        if size == 0 {
            return;
        } else if size == 1 {
            let lit = self.literal_at_clause_pos(clause_number, 0);
            self.queue_unit(lit);
        } else {
            let l0 = self.literal_at_clause_pos(clause_number, 0);
            let l1 = self.literal_at_clause_pos(clause_number, 1);
            self.add_watch(l0, clause_number);
            self.add_watch(l1, clause_number);
            let (start, _) = self.clauses_pt[clause_number];
            self.clauses_watches[clause_number] = (start, start + 1);
        }
    }

    fn update_watches(&mut self, clause_number: usize, from_var: usize, from_pos: usize) {
        if clause_number < self.clause_satisfied.len() && self.clause_satisfied[clause_number] {
            self.remove_watch(from_var, from_pos);
            return;
        }
        if self.clause_size(clause_number) <= 1 {
            return;
        }
        let (w1, w2) = self.clauses_watches[clause_number];
        let lit_w1 = self.clauses[w1];
        let lit_w2 = self.clauses[w2];
        debug_assert!(
            lit_w1.abs() as usize == from_var || lit_w2.abs() as usize == from_var
        );
        let (start, end) = self.clauses_pt[clause_number];
        let mut new_watch: Option<usize> = None;
        // Seek a non-false replacement (unassigned OR true). Seeking only
        // unassigned misses true literals in satisfied-but-unflagged clauses
        // (e.g. appended breaking clauses referencing older assignments)
        // and derives false conflicts. On unsatisfied clauses both coincide.
        for i in start..end {
            if i != w1 && i != w2 && self.assigned(self.clauses[i]) != -1 {
                new_watch = Some(i);
                break;
            }
        }
        match new_watch {
            None => {
                self.remove_watch(from_var, from_pos);
                if lit_w1.abs() as usize == from_var {
                    if self.assigned(lit_w2) == -1 {
                        self.conflict = true;
                    } else if self.assigned(lit_w2) == 0 {
                        self.queue_unit(lit_w2);
                    }
                } else if self.assigned(lit_w1) == -1 {
                    self.conflict = true;
                } else if self.assigned(lit_w1) == 0 {
                    self.queue_unit(lit_w1);
                }
            }
            Some(nw) => {
                self.remove_watch(from_var, from_pos);
                let lit = self.clauses[nw];
                self.add_watch(lit, clause_number);
                if lit_w1.abs() as usize == from_var {
                    self.clauses_watches[clause_number].0 = nw;
                } else {
                    self.clauses_watches[clause_number].1 = nw;
                }
            }
        }
    }

    // -- simplification helpers ------------------------------------------

    /// Mark all literals occurring in non-satisfied, unassigned positions.
    pub fn mark_literal_uses(&mut self) {
        for b in self.found_literal.iter_mut() {
            *b = false;
        }
        for i in 0..self.n_clauses() {
            if self.is_satisfied(i) {
                continue;
            }
            for j in 0..self.clause_size(i) {
                let lit = self.literal_at_clause_pos(i, j);
                if self.assigned(lit) == 0 {
                    self.found_literal[sat_to_graph(lit)] = true;
                }
            }
        }
    }

    pub fn is_literal_marked_used(&self, lit: i32) -> bool {
        self.found_literal[sat_to_graph(lit)]
    }

    /// Pure literals among the unassigned variables.
    pub fn pure_literals(&self) -> Vec<i32> {
        let mut out = Vec::new();
        for v in 1..=self.n_variables as i32 {
            if self.assigned(v) != 0 {
                continue;
            }
            let pos_used = self.found_literal[sat_to_graph(v)];
            let neg_used = self.found_literal[sat_to_graph(-v)];
            if pos_used && !neg_used {
                out.push(v);
            } else if neg_used && !pos_used {
                out.push(-v);
            }
        }
        out
    }

    /// Mark subsumed clauses satisfied. Returns number newly subsumed.
    /// Mirrors the bounded `mark_subsumed_clauses` heuristic.
    pub fn mark_subsumed_clauses(&mut self) -> usize {
        const SMALL: usize = 16;
        const BIG: usize = 1024;
        const MAX_USED: usize = 64;
        let n = self.n_clauses();
        let mut newly = 0;
        for i in 0..n {
            if self.is_satisfied(i) || self.clause_size(i) > SMALL {
                continue;
            }
            // Collect candidate subsuming clauses via occurrence lists.
            let mut in_clause = vec![false; 2 * self.n_variables];
            let mut lits = Vec::new();
            for j in 0..self.clause_size(i) {
                let lit = self.literal_at_clause_pos(i, j);
                if self.assigned(lit) != 0 {
                    continue;
                }
                lits.push(lit);
                in_clause[sat_to_graph(lit)] = true;
            }
            if lits.is_empty() {
                continue;
            }
            // Gather candidates.
            let mut seen = vec![false; n.max(1)];
            let mut candidates = Vec::new();
            for &lit in &lits {
                let g = sat_to_graph(lit);
                if self.literal_used_list[g].len() > MAX_USED {
                    continue;
                }
                for &c in self.literal_used_list[g].clone().iter() {
                    if self.clause_size(c) > BIG || c == i || self.is_satisfied(c) {
                        continue;
                    }
                    if !seen[c] {
                        seen[c] = true;
                        candidates.push(c);
                    }
                }
            }
            for c in candidates {
                if self.clause_size(c) <= self.clause_size(i) {
                    continue;
                }
                let mut ok = true;
                let mut count = 0;
                for j in 0..self.clause_size(c) {
                    let lit = self.literal_at_clause_pos(c, j);
                    if self.assigned(lit) != 0 {
                        continue;
                    }
                    if in_clause[sat_to_graph(lit)] {
                        count += 1;
                    } else {
                        ok = false;
                        break;
                    }
                }
                if ok && count == self.clause_size(i) {
                    self.clause_satisfied[c] = true;
                    newly += 1;
                    self.subsumptions_found += 1;
                }
            }
        }
        newly
    }

    /// Merge equivalence classes from complementary binary clauses
    /// (`(a b)` and `(-a -b)` imply `a <-> -b`).
    pub fn equivalent_literals(&mut self) {
        use std::collections::HashSet;
        let mut binary_db: HashSet<(i32, i32)> = HashSet::new();
        for i in 0..self.n_clauses() {
            if self.clause_size(i) != 2 {
                continue;
            }
            let mut lits = [
                self.literal_at_clause_pos(i, 0),
                self.literal_at_clause_pos(i, 1),
            ];
            lits.sort_unstable();
            let (a, b) = (lits[0], lits[1]);
            if binary_db.contains(&(-a, -b)) {
                self.equivalent.union(sat_to_graph(a), sat_to_graph(-b));
                self.equivalent.union(sat_to_graph(-a), sat_to_graph(b));
            }
            binary_db.insert((a, b));
        }
    }

    // -- accessors --------------------------------------------------------

    pub fn is_satisfied(&self, clause: usize) -> bool {
        self.clause_satisfied.get(clause).copied().unwrap_or(false)
    }

    pub fn satisfied_clauses(&self) -> usize {
        self.clause_satisfied
            .iter()
            .take(self.clauses_pt.len())
            .filter(|&&s| s)
            .count()
    }

    pub fn clause_size(&self, c: usize) -> usize {
        let (s, e) = self.clauses_pt[c];
        e - s
    }

    pub fn literal_at_clause_pos(&self, c: usize, i: usize) -> i32 {
        self.clauses[self.clauses_pt[c].0 + i]
    }

    pub fn n_clauses(&self) -> usize {
        self.clauses_pt.len()
    }

    pub fn n_variables(&self) -> usize {
        self.n_variables
    }

    pub fn n_total_clause_size(&self) -> usize {
        self.clauses.len()
    }

    pub fn n_len(&self) -> usize {
        self.clauses.len()
    }

    pub fn n_redundant_clauses(&self) -> usize {
        self.redundant_removed
    }

    pub fn n_redundant_literals(&self) -> usize {
        self.literals_removed
    }

    pub fn is_conflicting(&self) -> bool {
        self.conflict
    }

    /// Iterate over non-satisfied clauses as literal slices.
    pub fn active_clauses(&self) -> impl Iterator<Item = Vec<i32>> + '_ {
        (0..self.n_clauses()).filter_map(|c| {
            if self.is_satisfied(c) {
                return None;
            }
            let (s, e) = self.clauses_pt[c];
            Some(self.clauses[s..e].to_vec())
        })
    }

    pub fn reset_assignment(&mut self) {
        for b in self.clause_satisfied.iter_mut() {
            *b = false;
        }
        self.assignment = vec![0; 2 * self.n_variables];
        self.units.clear();
        for b in self.in_units.iter_mut() {
            *b = false;
        }
        self.conflict = false;
    }

    pub fn clear(&mut self) {
        *self = Self::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formula() -> CnfWl {
        let mut f = CnfWl::new();
        f.reserve(2, 3);
        f.add_clause(&[1, 2]);
        f.add_clause(&[-1]);
        f.add_clause(&[1, 1, 2]); // duplicate literal removed
        f
    }

    #[test]
    fn unit_propagates_to_conflict_free() {
        let mut f = formula();
        // -1 propagates, which then makes [1,2] unit on 2.
        assert_eq!(f.propagate(), 2);
        assert!(!f.is_conflicting());
        assert_eq!(f.assigned(-1), 1);
        assert_eq!(f.assigned(2), 1);
    }

    #[test]
    fn tautology_dropped() {
        let mut f = CnfWl::new();
        f.reserve(2, 2);
        f.add_clause(&[1, -1, 2]);
        assert_eq!(f.n_clauses(), 0);
        assert_eq!(f.n_redundant_clauses(), 1);
    }

    #[test]
    fn pure_detection() {
        let mut f = CnfWl::new();
        f.reserve(2, 2);
        f.add_clause(&[1, 2]);
        f.add_clause(&[1, -2]);
        f.mark_literal_uses();
        assert_eq!(f.pure_literals(), vec![1]);
    }
}
