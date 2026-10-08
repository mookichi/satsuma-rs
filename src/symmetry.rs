//! Symmetry abstraction.
//!
//! The original spends most of its code (`symmetries.h`, `hypergraph.h`,
//! `reorder.h`, plus the external `dejavu` graph isomorphism solver) on
//! discovering automorphisms of the model graph. That machinery is behind
//! this trait so the crate compiles and runs without a C++ dependency.
//!
//! Implement [`SymmetryProvider`] and pass it to
//! [`Preprocessor::with_provider`](crate::preprocessor::Preprocessor::with_provider)
//! to enable real symmetry breaking. The default
//! [`TrivialSymmetryProvider`] reports no symmetries, in which case the
//! preprocessor still performs symmetry-preserving simplification.

use crate::cnf::Cnf;
use std::collections::HashMap;

/// A permutation of graph vertices (`sat_to_graph` numbering), stored as
/// images: `image[v]` is where vertex `v` is mapped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Permutation {
    /// Full image array; identity outside the support.
    pub image: Vec<usize>,
    /// Support (moved points), for fast iteration.
    pub support: Vec<usize>,
}

impl Permutation {
    pub fn identity(domain: usize) -> Self {
        Self {
            image: (0..domain).collect(),
            support: Vec::new(),
        }
    }

    pub fn from_images(image: Vec<usize>) -> Self {
        let support = image
            .iter()
            .enumerate()
            .filter_map(|(i, &p)| if p != i { Some(i) } else { None })
            .collect();
        Self { image, support }
    }

    pub fn is_identity(&self) -> bool {
        self.support.is_empty()
    }

    /// Average support size helper for statistics.
    pub fn support_size(&self) -> usize {
        self.support.len()
    }
}

/// Partition of vertices into orbits (union-find), as produced by color
/// refinement or Schreier-Sims orbits.
#[derive(Debug, Clone, Default)]
pub struct OrbitPartition {
    parent: Vec<usize>,
}

impl OrbitPartition {
    pub fn new(domain: usize) -> Self {
        Self {
            parent: (0..domain).collect(),
        }
    }

    pub fn find(&mut self, x: usize) -> usize {
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut cur = x;
        while self.parent[cur] != root {
            let next = self.parent[cur];
            self.parent[cur] = root;
            cur = next;
        }
        root
    }

    pub fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent[ra] = rb;
        }
    }

    /// Number of non-trivial orbits.
    pub fn n_orbits(&mut self) -> usize {
        let mut reps = std::collections::HashSet::new();
        for i in 0..self.parent.len() {
            reps.insert(self.find(i));
        }
        reps.len()
    }
}

/// Result of symmetry detection: generators plus an orbit approximation.
#[derive(Debug, Clone, Default)]
pub struct SymmetryGroup {
    pub generators: Vec<Permutation>,
    /// Approximate orbits from color refinement (may over-approximate).
    pub orbit_approx: OrbitPartition,
    /// Suggested lex order: 0-based variable indices.
    pub order: Vec<usize>,
}

impl SymmetryGroup {
    pub fn empty(domain: usize) -> Self {
        Self {
            generators: Vec::new(),
            orbit_approx: OrbitPartition::new(domain),
            order: Vec::new(),
        }
    }

    pub fn n_generators(&self) -> usize {
        self.generators.len()
    }
}

/// Source of automorphisms for the preprocessor.
///
/// The original's `symmetries` class implements this role with `dejavu`,
/// Johnson / row / row-column structure detection, and Schreier-Sims.
/// Custom providers receive the deduplicated formula and return generators
/// acting on graph vertices of size `2 * n_variables`.
pub trait SymmetryProvider {
    /// Detect symmetries of `formula`. Called once per iteration.
    fn detect(&mut self, formula: &Cnf) -> SymmetryGroup;
    /// Sync search limits from the preprocessor config (default: no-op).
    fn set_limits(&mut self, _time_budget_ms: u64, _max_pairs: usize, _max_nodes: u64) {}
    /// Enable/disable generator optimization (default: no-op).
    fn set_optimize(&mut self, _optimize: bool) {}
}

/// Default provider: reports no symmetries.
///
/// The pipeline then reduces to symmetry-preserving simplification plus
/// AMO completion — still useful, and equisatisfiability is trivially
/// preserved.
#[derive(Debug, Clone, Copy, Default)]
pub struct TrivialSymmetryProvider;

impl SymmetryProvider for TrivialSymmetryProvider {
    fn detect(&mut self, formula: &Cnf) -> SymmetryGroup {
        let mut group = SymmetryGroup::empty(2 * formula.n_variables());
        group.order = (0..formula.n_variables()).collect();
        group
    }
}

/// One round of color refinement on the variable-incidence graph.
///
/// Returns a signature per variable; equal signatures mean "possibly
/// symmetric". This mirrors the *approximation* step of the original
/// (`make graph and approximate orbits`) without claiming exactness:
/// it is exposed so future providers and CLI diagnostics can order
/// variables, not as a symmetry proof.
pub fn approximate_orbits(formula: &Cnf) -> HashMap<usize, Vec<usize>> {
    // Signature: sorted multiset of (clause size, #occurrences of co-members).
    let mut sigs: HashMap<Vec<usize>, Vec<usize>> = HashMap::new();
    for v in 0..formula.n_variables() {
        let mut sig = vec![0usize; 4];
        for &c in &formula.occurrence_lists()[v] {
            let sz = formula.clause_size(c).min(16);
            sig[0] += 1;
            sig[1] += sz;
            sig[2] += sz * sz;
            sig[3] += formula.clause(c).iter().map(|l| l.abs() as usize).sum::<usize>();
        }
        sigs.entry(sig).or_default().push(v);
    }
    // Re-key by class index for a stable representation.
    sigs.into_values()
        .enumerate()
        .map(|(i, vars)| (i, vars))
        .collect()
}
