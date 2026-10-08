//! Automorphism discovery via individualization-refinement isomorphism search.
//!
//! For each pair of literals sharing a refined color, we search for an
//! isomorphism between the model graph individualized at `u` and the same
//! graph individualized at `v`. Such an isomorphism is an automorphism
//! mapping `u` to `v`. Every candidate is **verified exactly** against the
//! formula (all clause images must be present), so search incompleteness
//! (budgets, caps) can only weaken breaking, never break equisatisfiability.
//!
//! Soundness note: breaking any subgroup of the automorphism group with
//! lex-leader constraints preserves satisfiability in both directions, so a
//! partial generating set is always safe.

use crate::cnf::Cnf;
use crate::graph::{histogram, is_discrete, refine, ModelGraph};
use crate::literal::{graph_to_sat, sat_to_graph};
use crate::symmetry::{OrbitPartition, Permutation, SymmetryGroup, SymmetryProvider};
use std::time::Instant;

/// Limits for the search; bounding these only reduces completeness.
#[derive(Debug, Clone, Copy)]
pub struct SearchLimits {
    /// Total wall-clock budget for one `detect` call.
    pub time_budget_ms: u64,
    /// Max `u -> v` pair attempts per refined literal cell.
    pub max_pairs_per_cell: usize,
    /// Max refinement/search recursion calls per pair (bounds worst pairs).
    pub max_nodes_per_pair: u64,
    /// Whether to shorten supports via group-preserving products.
    pub optimize_generators: bool,
}

impl Default for SearchLimits {
    fn default() -> Self {
        Self {
            time_budget_ms: 10_000,
            max_pairs_per_cell: 512,
            max_nodes_per_pair: 50_000,
            optimize_generators: false,
        }
    }
}

struct Ctx<'a> {
    adj: &'a [Vec<usize>],
    /// Adjacency as hash sets for O(1) edge tests at leaves.
    adj_set: &'a [std::collections::HashSet<usize>],
    deadline: Option<Instant>,
    calls: u64,
    node_cap: u64,
}

impl Ctx<'_> {
    fn timed_out(&self) -> bool {
        self.calls >= self.node_cap
            || self.deadline.is_some_and(|d| Instant::now() >= d)
    }
}

/// Search an isomorphism between individualized copies.
/// Fresh individualization colors come from `fresh` (shared counter, so both
/// sides use identical values in lockstep); they must never collide with
/// existing colors.
fn search(
    ctx: &mut Ctx,
    col_a: Vec<usize>,
    col_b: Vec<usize>,
    fresh: &mut usize,
) -> Option<Vec<usize>> {
    ctx.calls += 1;
    if ctx.calls % 1024 == 0 && ctx.timed_out() {
        return None;
    }
    let col_a = refine(ctx.adj, &col_a);
    let col_b = refine(ctx.adj, &col_b);
    if histogram(&col_a) != histogram(&col_b) {
        return None;
    }
    if is_discrete(&col_a) {
        // Pair singletons by color (numbering is cross-graph consistent).
        let n = col_a.len();
        // Map color -> vertex for B (colors may be large; use hashmap).
        let mut b_of: std::collections::HashMap<usize, usize> =
            std::collections::HashMap::with_capacity(n);
        for (w, &c) in col_b.iter().enumerate() {
            b_of.insert(c, w);
        }
        let mut perm = vec![0usize; n];
        for (a, &c) in col_a.iter().enumerate() {
            match b_of.get(&c) {
                Some(&w) => perm[a] = w,
                None => return None,
            }
        }
        // Verify adjacency preservation.
        for a in 0..n {
            for &b in &ctx.adj[a] {
                if !ctx.adj_set[perm[a]].contains(&perm[b]) {
                    return None;
                }
            }
        }
        return Some(perm);
    }
    // Target cell: smallest non-singleton cell in vertex order.
    let mut by_color: std::collections::HashMap<usize, Vec<usize>> =
        std::collections::HashMap::new();
    for (a, &c) in col_a.iter().enumerate() {
        by_color.entry(c).or_default().push(a);
    }
    let mut target: Option<usize> = None; // representative vertex of target cell
    for a in 0..col_a.len() {
        let cell = &by_color[&col_a[a]];
        if cell.len() > 1
            && target.is_none_or(|t| cell.len() < by_color[&col_a[t]].len())
        {
            target = Some(a);
            if cell.len() == 2 {
                break;
            }
        }
    }
    let x = target?;
    let color = col_a[x];
    let bcell: Vec<usize> = col_b
        .iter()
        .enumerate()
        .filter_map(|(w, &c)| (c == color).then_some(w))
        .collect();
    for w in bcell {
        if ctx.timed_out() {
            return None;
        }
        let f = *fresh;
        *fresh += 1;
        let mut na = col_a.clone();
        let mut nb = col_b.clone();
        na[x] = f;
        nb[w] = f;
        if let Some(p) = search(ctx, na, nb, fresh) {
            return Some(p);
        }
    }
    None
}

/// Find an automorphism mapping `u` to `v` (both literal vertices).
/// `col_a_stable` is the fully refined coloring with `u` individualized
/// using marker `marker` (shared across all pairs of a cell); the B side
/// marks `v` with the same value, keeping pairing consistent.
fn find_auto(
    adj: &[Vec<usize>],
    adj_set: &[std::collections::HashSet<usize>],
    col_a_stable: &[usize],
    base: &[usize],
    marker: usize,
    v: usize,
    deadline: Option<Instant>,
    node_cap: u64,
) -> (Option<Vec<usize>>, u64) {
    let mut col_b = base.to_vec();
    col_b[v] = marker;
    let mut ctx = Ctx { adj, adj_set, deadline, calls: 0, node_cap };
    let mut fresh = marker + 1;
    let r = search(&mut ctx, col_a_stable.to_vec(), col_b, &mut fresh);
    (r, ctx.calls)
}

/// Compose permutations: apply `first`, then `second`.
fn compose(first: &[usize], second: &[usize]) -> Vec<usize> {
    first.iter().map(|&v| second[v]).collect()
}

/// Invert a permutation.
fn invert(perm: &[usize]) -> Vec<usize> {
    let mut inv = vec![0usize; perm.len()];
    for (i, &p) in perm.iter().enumerate() {
        inv[p] = i;
    }
    inv
}

/// Shorten generator supports by trying products `g·h^±1` (group-preserving:
/// `g` is recoverable as `(g·h)·h⁻¹`). Mirrors the spirit of the original's
/// generator optimization: short generators give tight lex constraints.
fn shorten_supports(generators: &mut Vec<Permutation>, passes: usize) {
    for _ in 0..passes {
        let mut changed = false;
        // Only multiply by reasonably short elements (bound the work).
        let shorts: Vec<Vec<usize>> = generators
            .iter()
            .filter(|g| g.support_size() <= 64)
            .map(|g| g.image.clone())
            .collect();
        if shorts.is_empty() {
            break;
        }
        for g in generators.iter_mut() {
            let cur = g.support_size();
            if cur <= 4 {
                continue;
            }
            let mut best = g.image.clone();
            let mut best_n = cur;
            for h in &shorts {
                if *h == best {
                    continue; // g·g⁻¹ = identity is useless
                }
                for cand in [compose(&best, h), compose(&best, &invert(h))] {
                    let n = cand.iter().enumerate().filter(|(i, &p)| p != *i).count();
                    if n < best_n {
                        best_n = n;
                        best = cand;
                    }
                }
            }
            if best_n < cur {
                *g = Permutation::from_images(best);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}
/// Exact check: does `perm` (full-graph images) preserve the formula?
/// Only the literal part is examined; images must stay literal vertices.
/// Assigned literals must additionally be stabilized setwise (defense in
/// depth alongside unit coloring in the model graph).
fn verify_automorphism(db: &Cnf, perm: &[usize]) -> bool {
    let n_literals = 2 * db.n_variables();
    if perm.len() < n_literals {
        return false;
    }
    // Literal vertices must map to literal vertices (color classes separate
    // them structurally, but check explicitly for safety).
    for v in 0..n_literals {
        if perm[v] >= n_literals {
            return false;
        }
    }
    if db.unit_true.len() == n_literals {
        for v in 0..n_literals {
            // Both the literal and its negation must stay in their
            // assigned-status class (stabilize assigned sets setwise).
            if db.unit_true[v] != db.unit_true[perm[v]] {
                return false;
            }
            if db.unit_true[crate::literal::graph_negate(v)]
                != db.unit_true[crate::literal::graph_negate(perm[v])]
            {
                return false;
            }
        }
    }
    let mut image = Vec::with_capacity(8);
    for c in 0..db.n_clauses() {
        image.clear();
        for &lit in db.clause(c) {
            image.push(graph_to_sat(perm[sat_to_graph(lit)]));
        }
        if !db.is_clause(&image) {
            return false;
        }
    }
    true
}

/// Result of detection: verified generators plus a variable order.
pub struct Detection {
    /// Generators as literal-vertex permutations (`image.len() == 2*n_vars`).
    pub generators: Vec<Permutation>,
    /// Suggested lex order: 0-based variable indices, same-cell vars adjacent.
    pub order: Vec<usize>,
    /// Refined literal cells (orbit over-approximation).
    pub approx_cells: Vec<Vec<usize>>,
    /// Pair searches attempted.
    pub pair_attempts: usize,
}

/// Detect symmetries of `db` within `limits`.
pub fn detect_automorphisms(db: &Cnf, limits: SearchLimits) -> Detection {
    let n_vars = db.n_variables();
    let natural: Vec<usize> = (0..n_vars).collect();
    if n_vars == 0 || db.n_clauses() == 0 {
        return Detection {
            generators: Vec::new(),
            order: natural,
            approx_cells: Vec::new(),
            pair_attempts: 0,
        };
    }
    let graph = ModelGraph::build(db);
    let base = refine(&graph.adj, &graph.base_color);
    let n_literals = graph.n_literals;

    // Variable order: group same-cell variables, stable by id.
    let mut vars: Vec<usize> = (0..n_vars).collect();
    vars.sort_by_key(|&v| (base[sat_to_graph((v + 1) as i32)], v));

    let deadline = Some(Instant::now() + std::time::Duration::from_millis(limits.time_budget_ms));
    let t_start = Instant::now();
    let mut t_search = std::time::Duration::ZERO;
    let mut t_verify = std::time::Duration::ZERO;
    let mut total_nodes: u64 = 0;    let adj_set: Vec<std::collections::HashSet<usize>> = graph
        .adj
        .iter()
        .map(|nbs| nbs.iter().copied().collect())
        .collect();

    let mut generators = Vec::new();
    let mut seen: std::collections::HashSet<Vec<usize>> = std::collections::HashSet::new();
    let mut pair_attempts = 0;
    let mut timed_out = false;

    let cells = ModelGraph::literal_cells(&base, n_literals);
    let marker = base.iter().max().copied().unwrap_or(0) + 1;
    for cell in &cells {
        if cell.len() < 2 || timed_out {
            continue;
        }
        // Refine the u-individualized side once per cell (shared by all pairs).
        let mut col_a = base.clone();
        col_a[cell[0]] = marker;
        let col_a = refine(&graph.adj, &col_a);
        let mut attempts = 0;
        for &v in &cell[1..] {
            if attempts >= limits.max_pairs_per_cell {
                break;
            }
            if deadline.is_some_and(|d| Instant::now() >= d) {
                timed_out = true;
                break;
            }
            attempts += 1;
            pair_attempts += 1;
            let ts = Instant::now();
            let (found, nodes) = find_auto(
                &graph.adj,
                &adj_set,
                &col_a,
                &base,
                marker,
                v,
                deadline,
                limits.max_nodes_per_pair,
            );
            t_search += ts.elapsed();
            total_nodes += nodes;
            if let Some(perm) = found
            {
                let tv = Instant::now();
                let ok = verify_automorphism(db, &perm);
                t_verify += tv.elapsed();
                if ok {
                    let image = perm[..n_literals].to_vec();
                    // Skip identity and duplicates.
                    if image.iter().enumerate().any(|(i, &p)| p != i) && seen.insert(image.clone()) {
                        generators.push(Permutation::from_images(image));
                    }
                }
            }
        }
    }

    // Optional support shortening (group-preserving, `--opt`).
    if limits.optimize_generators {
        shorten_supports(&mut generators, 16);
    }

    // Verified generators strengthen breaking — keep them all; the cap is a
    // pure safety bound against pathological memory blowup.
    generators.sort_by_key(|g| g.support_size());
    generators.truncate(4096);

    if std::env::var("SATSUMA_PROFILE").is_ok() {
        eprintln!(
            "c [symprofile total={:.1}ms search={:.1}ms verify={:.1}ms pairs={} nodes={} gens={}]",
            t_start.elapsed().as_secs_f64() * 1000.0,
            t_search.as_secs_f64() * 1000.0,
            t_verify.as_secs_f64() * 1000.0,
            pair_attempts,
            total_nodes,
            generators.len()
        );
    }

    Detection { generators, order: vars, approx_cells: cells, pair_attempts }
}

/// Orbits of literal vertices under `generators` (exact, via union-find).
pub fn literal_orbits(n_vars: usize, generators: &[Permutation]) -> OrbitPartition {
    let mut orbits = OrbitPartition::new(2 * n_vars);
    for g in generators {
        for (v, &img) in g.image.iter().enumerate() {
            orbits.union(v, img);
        }
    }
    orbits
}

/// Default [`SymmetryProvider`](crate::symmetry::SymmetryProvider): discovers
/// verified automorphisms of the model graph and breaks (a subgroup of) them
/// with lex-leader constraints. Pure Rust; no external GI library.
#[derive(Debug, Clone, Copy)]
pub struct GraphAutomorphismProvider {
    /// Wall-clock budget per detection round (ms).
    pub time_budget_ms: u64,
    /// Max pair attempts per refined cell.
    pub max_pairs_per_cell: usize,
    /// Max search nodes per pair.
    pub max_nodes_per_pair: u64,
    /// Whether to shorten supports via group-preserving products (`--opt`).
    pub optimize_generators: bool,
}

impl Default for GraphAutomorphismProvider {
    fn default() -> Self {
        Self {
            time_budget_ms: 10_000,
            max_pairs_per_cell: 512,
            max_nodes_per_pair: 50_000,
            optimize_generators: false,
        }
    }
}

impl SymmetryProvider for GraphAutomorphismProvider {
    fn detect(&mut self, formula: &Cnf) -> SymmetryGroup {
        let det = detect_automorphisms(
            formula,
            SearchLimits {
                time_budget_ms: self.time_budget_ms,
                max_pairs_per_cell: self.max_pairs_per_cell,
                max_nodes_per_pair: self.max_nodes_per_pair,
                optimize_generators: self.optimize_generators,
            },
        );
        let mut approx = OrbitPartition::new(2 * formula.n_variables());
        for cell in &det.approx_cells {
            for w in &cell[1..] {
                approx.union(cell[0], *w);
            }
        }
        SymmetryGroup { generators: det.generators, orbit_approx: approx, order: det.order }
    }

    fn set_limits(&mut self, time_budget_ms: u64, max_pairs: usize, max_nodes: u64) {
        self.time_budget_ms = time_budget_ms;
        self.max_pairs_per_cell = max_pairs;
        self.max_nodes_per_pair = max_nodes;
    }

    fn set_optimize(&mut self, optimize: bool) {
        self.optimize_generators = optimize;
    }
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
    fn finds_swap() {
        let db = db_of(&[vec![1, 2], vec![-1, -2]], 2);
        let det = detect_automorphisms(&db, SearchLimits { time_budget_ms: 5000, max_pairs_per_cell: 16, max_nodes_per_pair: 50_000, optimize_generators: true });
        assert!(!det.generators.is_empty(), "swap should be found");
        // Every reported generator must be exact (verified internally, re-check).
        assert!(det.generators.iter().all(|g| verify_automorphism(&db, &g.image)));
    }

    #[test]
    fn rigid_formula_has_no_generators() {
        let db = db_of(&[vec![1], vec![1, 2]], 2);
        let det = detect_automorphisms(&db, SearchLimits { time_budget_ms: 5000, max_pairs_per_cell: 16, max_nodes_per_pair: 50_000, optimize_generators: true });
        assert!(det.generators.is_empty());
    }

    #[test]
    fn finds_row_transposition() {
        // 2x2 matrix, rows interchangeable: (x11 \/ x12) /\ (x21 \/ x22) + row-internal links.
        // vars: 1=(1,1) 2=(1,2) 3=(2,1) 4=(2,2)
        let db = db_of(&[vec![1, 2], vec![3, 4], vec![-1, -3], vec![-2, -4]], 4);
        let det = detect_automorphisms(&db, SearchLimits { time_budget_ms: 5000, max_pairs_per_cell: 32, max_nodes_per_pair: 50_000, optimize_generators: true });
        assert!(!det.generators.is_empty());
        assert!(det.generators.iter().all(|g| verify_automorphism(&db, &g.image)));
    }
}
