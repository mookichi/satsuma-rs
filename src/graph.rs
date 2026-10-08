//! Model graph of a CNF formula plus color refinement (WL-1).
//!
//! Construction (standard, cf. BreakID): one vertex per literal
//! (numbered with [`sat_to_graph`](crate::literal::sat_to_graph)), one
//! vertex per clause. Complement edges `(l, ¬l)` force automorphisms to
//! respect negation; incidence edges `(literal, clause)` encode the
//! formula. Colors are isomorphism-invariant: literals share a base color,
//! clauses are colored by size. Any automorphism of this colored graph,
//! restricted to literal vertices, is a symmetry of the formula (verified
//! exactly by the caller via clause images).

use crate::cnf::Cnf;
use crate::literal::{graph_negate, sat_to_graph};
use std::collections::BTreeMap;

/// Colored undirected graph, adjacency as sorted vectors.
#[derive(Debug, Clone)]
pub struct ModelGraph {
    /// Total vertices: `2*n_vars` literal vertices followed by clause vertices.
    pub n: usize,
    /// Number of literal vertices (`2 * n_vars`).
    pub n_literals: usize,
    pub adj: Vec<Vec<usize>>,
    /// Initial colors: `0` for literals, `1 + min(size, 255)` for clauses.
    pub base_color: Vec<usize>,
}

impl ModelGraph {
    /// Build the model graph of a deduplicated formula.
    pub fn build(db: &Cnf) -> Self {
        let n_vars = db.n_variables();
        let n_literals = 2 * n_vars;
        let m = db.n_clauses();
        let n = n_literals + m;
        let mut adj = vec![Vec::new(); n];
        let mut base_color = vec![0usize; n];

        // Complement edges: l -- ¬l.
        for v in 1..=n_vars as i32 {
            let a = sat_to_graph(v);
            let b = sat_to_graph(-v);
            adj[a].push(b);
            adj[b].push(a);
        }
        // Incidence edges + clause colors.
        for c in 0..m {
            let cv = n_literals + c;
            base_color[cv] = 1 + db.clause_size(c).min(255);
            for &lit in db.clause(c) {
                let lv = sat_to_graph(lit);
                adj[lv].push(cv);
                adj[cv].push(lv);
            }
        }
        // Assigned literals get distinguished colors (both polarities):
        // symmetries must stabilize the assigned set setwise, otherwise
        // breaking them is unsound. True symmetries always do, so nothing
        // is lost.
        if db.unit_true.len() == n_literals && db.unit_true.iter().any(|&u| u) {
            let max_c = base_color.iter().max().copied().unwrap_or(0);
            let (true_c, false_c) = (max_c + 1, max_c + 2);
            for v in 0..n_literals {
                if v < db.unit_true.len() && db.unit_true[v] {
                    base_color[v] = true_c;
                } else if db.unit_true[graph_negate(v)] {
                    base_color[v] = false_c;
                }
            }
        }
        for nbrs in adj.iter_mut() {
            nbrs.sort_unstable();
            nbrs.dedup();
        }
        Self { n, n_literals, adj, base_color }
    }

    /// Cells of a coloring restricted to literal vertices, in vertex order.
    pub fn literal_cells(color: &[usize], n_literals: usize) -> Vec<Vec<usize>> {
        let mut order: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for v in 0..n_literals {
            order.entry(color[v]).or_default().push(v);
        }
        order.into_values().collect()
    }
}

/// One round-stable color refinement (1-dim Weisfeiler-Leman).
///
/// Numbering is canonical (sorted distinct-key order), hence
/// labeling-independent: equally-colored graphs get identical numbering.
/// Required to pair singletons across individualized copies in search.
/// Hot path: signatures allocated once per vertex per round; ids assigned by
/// sorting indices (no hashing of signatures, no tree insertions).
pub fn refine(adj: &[Vec<usize>], color: &[usize]) -> Vec<usize> {
    let n = color.len();
    if n == 0 {
        return Vec::new();
    }
    let mut col = color.to_vec();
    let mut sigs: Vec<(usize, Vec<usize>)> = Vec::with_capacity(n);
    let mut idx: Vec<usize> = (0..n).collect();
    let mut next = vec![0usize; n];
    loop {
        // Pass 1: signatures (one alloc per vertex).
        sigs.clear();
        for v in 0..n {
            let mut sig = Vec::with_capacity(adj[v].len());
            sig.extend(adj[v].iter().map(|&w| col[w]));
            sig.sort_unstable();
            sigs.push((col[v], sig));
        }
        // Pass 2: canonical ids by sorted-key runs (ordering matches
        // BTreeSet key order, hence canonical).
        idx.sort_by(|&a, &b| sigs[a].cmp(&sigs[b]));
        let mut id = 0;
        next[idx[0]] = 0;
        for w in idx.windows(2) {
            if sigs[w[1]] != sigs[w[0]] {
                id += 1;
            }
            next[w[1]] = id;
        }
        if next == col {
            return col;
        }
        std::mem::swap(&mut col, &mut next);
    }
}

/// Histogram of a coloring (sorted color multiset), for pruning.
pub fn histogram(color: &[usize]) -> Vec<usize> {
    let mut h = color.to_vec();
    h.sort_unstable();
    h
}

/// True when every vertex has a unique color.
pub fn is_discrete(color: &[usize]) -> bool {
    let mut set = std::collections::HashSet::with_capacity(color.len());
    color.iter().all(|c| set.insert(c))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn db_of(clauses: &[Vec<i32>], n_vars: usize) -> Cnf {
        let mut db = Cnf::new();
        db.reserve(n_vars, clauses.len());
        for c in clauses {
            db.add_clause(c);
        }
        db
    }

    #[test]
    fn refinement_splits_unit_var() {
        // x appears in a unit clause, y does not -> different colors.
        let db = db_of(&[vec![1], vec![1, 2]], 2);
        let g = ModelGraph::build(&db);
        let col = refine(&g.adj, &g.base_color);
        assert_ne!(col[sat_to_graph(1)], col[sat_to_graph(2)]);
    }

    #[test]
    fn symmetric_vars_share_color() {
        // {1,2},{-1,-2}: 1 and 2 interchangeable.
        let db = db_of(&[vec![1, 2], vec![-1, -2]], 2);
        let g = ModelGraph::build(&db);
        let col = refine(&g.adj, &g.base_color);
        assert_eq!(col[sat_to_graph(1)], col[sat_to_graph(2)]);
        assert_eq!(col[sat_to_graph(-1)], col[sat_to_graph(-2)]);
    }

    #[test]
    fn clause_color_encodes_size() {
        let db = db_of(&[vec![1], vec![1, 2, 3]], 3);
        let g = ModelGraph::build(&db);
        assert_ne!(g.base_color[g.n_literals], g.base_color[g.n_literals + 1]);
    }
}
