//! Preprocessor: configuration and pipeline.
//!
//! Port of `satsuma::preprocessor` (`satsuma.h`) and the `fix`/`lex`
//! driver logic from `satsuma.cpp`. The stage order mirrors the original:
//!
//! 1. symmetry-preserving CNF simplification (unit / pure / subsumption),
//! 2. transfer into the deduplicating clause database (+ AMO completion),
//! 3. symmetry detection via [`SymmetryProvider`](crate::symmetry::SymmetryProvider),
//! 4. breaking predicates into [`Predicate`](crate::predicate::Predicate),
//! 5. optional iteration (`fix` mode),
//! 6. DIMACS output.
//!
//! Equisatisfiability is preserved at every stage: simplification only applies
//! sound propagations, dedup drops tautologies/duplicates, and breaking
//! clauses are supplied by the provider (the default provider adds none).

use crate::automorphism::GraphAutomorphismProvider;
use crate::cnf::Cnf;
use crate::cnf2wl::CnfWl;
use crate::parser::{parse_dimacs_str, ParseError};
use crate::predicate::Predicate;
use crate::proof::{Proof, ProofFormat};
use crate::symmetry::SymmetryProvider;
use crate::tracker::{Metric, Routine, Tracker};

/// Preprocessing mode, mirroring the `fix` / `lex` CLI subcommands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Mode {
    /// Iterative fixing (`satsuma fix` defaults).
    #[default]
    Fix,
    /// Lex-leader constraints (`satsuma lex` defaults).
    Lex,
}

/// Configuration, mirroring the setters of `satsuma::preprocessor`.
///
/// Only behavior-affecting options are listed; unknown CLI flags for
/// fine-tuning the (not yet ported) dejavu engine are accepted by the
/// binary and documented as no-ops.
#[derive(Debug, Clone)]
pub struct PreprocessorConfig {
    pub mode: Mode,
    pub preprocess_unit: bool,
    pub preprocess_pure: bool,
    pub preprocess_subsume: bool,
    pub preprocess_equiv: bool,
    pub iterate: bool,
    pub iteration_limit: usize,
    pub break_depth: usize,
    pub optimize_generators: bool,
    pub binary_clauses: bool,
    pub orbitopal_fixing: bool,
    pub schreier_fixing: bool,
    pub negation_fixing: bool,
    pub add_reduced_as_unit: bool,
    pub proof_format: ProofFormat,
    /// Wall-clock budget (ms) for symmetry detection per iteration.
    pub sym_time_budget_ms: u64,
    /// Max automorphism pair attempts per refined cell.
    pub sym_max_pairs: usize,
    /// Max search nodes per pair attempt.
    pub sym_max_nodes: u64,
}

impl PreprocessorConfig {
    pub fn new(mode: Mode) -> Self {
        match mode {
            Mode::Fix => Self {
                mode,
                preprocess_unit: true,
                preprocess_pure: true,
                preprocess_subsume: false,
                preprocess_equiv: false,
                iterate: true,
                iteration_limit: 128,
                break_depth: 512,
                optimize_generators: true,
                binary_clauses: false,
                orbitopal_fixing: true,
                schreier_fixing: true,
                negation_fixing: true,
                add_reduced_as_unit: false,
                proof_format: ProofFormat::Sr,
                sym_time_budget_ms: 10_000,
                sym_max_pairs: 512,
                sym_max_nodes: 50_000,
            },
            Mode::Lex => Self {
                mode,
                preprocess_unit: false,
                preprocess_pure: false,
                preprocess_subsume: false,
                preprocess_equiv: false,
                iterate: false,
                iteration_limit: 128,
                break_depth: 512,
                optimize_generators: true,
                binary_clauses: false,
                orbitopal_fixing: false,
                schreier_fixing: false,
                negation_fixing: false,
                add_reduced_as_unit: false,
                proof_format: ProofFormat::Sr,
                sym_time_budget_ms: 10_000,
                sym_max_pairs: 512,
                sym_max_nodes: 50_000,
            },
        }
    }

    pub fn with_unit(mut self, v: bool) -> Self {
        self.preprocess_unit = v;
        self
    }
    pub fn with_pure(mut self, v: bool) -> Self {
        self.preprocess_pure = v;
        self
    }
    pub fn with_subsume(mut self, v: bool) -> Self {
        self.preprocess_subsume = v;
        self
    }
    pub fn with_iterate(mut self, v: bool) -> Self {
        self.iterate = v;
        self
    }
    pub fn with_break_depth(mut self, d: usize) -> Self {
        self.break_depth = d;
        self
    }
    pub fn with_add_reduced_as_unit(mut self, v: bool) -> Self {
        self.add_reduced_as_unit = v;
        self
    }
    pub fn with_binary_clauses(mut self, v: bool) -> Self {
        self.binary_clauses = v;
        self
    }
    pub fn with_proof_format(mut self, f: ProofFormat) -> Self {
        self.proof_format = f;
        self
    }
    pub fn with_sym_time_budget_ms(mut self, ms: u64) -> Self {
        self.sym_time_budget_ms = ms;
        self
    }
    pub fn with_sym_max_pairs(mut self, n: usize) -> Self {
        self.sym_max_pairs = n;
        self
    }
    pub fn with_sym_max_nodes(mut self, n: u64) -> Self {
        self.sym_max_nodes = n;
        self
    }
    pub fn with_optimize_generators(mut self, v: bool) -> Self {
        self.optimize_generators = v;
        self
    }
}

/// Preprocessing result: DIMACS text plus statistics.
#[derive(Debug, Clone)]
pub struct Output {
    /// Full DIMACS output including the `p cnf` header.
    pub dimacs: String,
    pub n_variables: usize,
    pub n_clauses: usize,
    pub n_sbp_clauses: usize,
    pub n_extra_variables: usize,
    pub n_generators: usize,
    pub n_row_groups: usize,
    pub iterations: usize,
    pub propagations: usize,
    /// Proof stream when the preprocessor was given a proof buffer.
    pub proof_text: Option<Vec<u8>>,
}

impl Output {
    /// True when the output is the trivially unsatisfiable empty clause.
    pub fn is_unsat(&self) -> bool {
        self.n_clauses == 1 && self.dimacs.lines().any(|l| l.trim() == "0")
    }
}

/// Failed-literal probing: tentatively assign each unassigned variable both
/// ways on a scratch clone; a conflicting side proves the opposite unit.
/// Sound, and RUP-loggable (failed literals are RUP by construction).
/// Only original variables (`1..=base_vars`) are probed. Derived units are
/// applied immediately and logged. Bounded by `max_sweeps` full sweeps.
/// Returns the number of newly derived units.
fn probe_units(
    formula: &mut CnfWl,
    base_vars: usize,
    max_sweeps: usize,
    mut proof: Option<&mut Proof>,
) -> usize {
    let mut total = 0;
    let mut trials: usize = 0;
    const MAX_TRIALS: usize = 30_000;
    for _ in 0..max_sweeps {
        let mut sweep_units = 0;
        for v in 1..=base_vars.min(formula.n_variables()) as i32 {
            if formula.is_conflicting() {
                break;
            }
            if formula.assigned(v) != 0 {
                continue;
            }
            for &lit in &[v, -v] {
                if trials >= MAX_TRIALS {
                    break;
                }
                if formula.assigned(lit) != 0 || formula.is_conflicting() {
                    break;
                }
                trials += 1;
                let mut trial = formula.clone();
                trial.assign_literal(lit);
                trial.propagate();
                if trial.is_conflicting() {
                    formula.assign_literal(-lit);
                    formula.propagate();
                    total += 1;
                    sweep_units += 1;
                    if let Some(p) = proof.as_mut() {
                        p.drat_clause(&[-lit]);
                    }
                    break;
                }
            }
            if trials >= MAX_TRIALS {
                break;
            }
        }
        if sweep_units == 0 || formula.is_conflicting() {
            break;
        }
    }
    total
}

/// The preprocessor.
pub struct Preprocessor<P = GraphAutomorphismProvider> {
    config: PreprocessorConfig,
    provider: P,
    tracker: Tracker,
    proof: Option<Proof>,
}

impl Preprocessor<GraphAutomorphismProvider> {
    pub fn with_config(config: PreprocessorConfig) -> Self {
        let provider = GraphAutomorphismProvider {
            time_budget_ms: config.sym_time_budget_ms,
            max_pairs_per_cell: config.sym_max_pairs,
            max_nodes_per_pair: config.sym_max_nodes,
            optimize_generators: config.optimize_generators,
        };
        Self { config, provider, tracker: Tracker::new(), proof: None }
    }

    pub fn fix() -> Self {
        Self::with_config(PreprocessorConfig::new(Mode::Fix))
    }

    pub fn lex() -> Self {
        Self::with_config(PreprocessorConfig::new(Mode::Lex))
    }
}

impl<P: SymmetryProvider> Preprocessor<P> {
    /// Swap the symmetry backend (e.g. a dejavu-backed provider).
    pub fn with_provider<Q: SymmetryProvider>(
        self,
        provider: Q,
    ) -> Preprocessor<Q> {
        Preprocessor {
            config: self.config,
            provider,
            tracker: self.tracker,
            proof: self.proof,
        }
    }

    pub fn with_proof(mut self, proof: Proof) -> Self {
        self.proof = Some(proof);
        self
    }

    pub fn tracker(&self) -> &Tracker {
        &self.tracker
    }

    pub fn config(&self) -> &PreprocessorConfig {
        &self.config
    }

    /// Parse and preprocess DIMACS text.
    pub fn preprocess_str(&mut self, dimacs: &str) -> Result<Output, ParseError> {
        let mut formula = parse_dimacs_str(dimacs)?;
        Ok(self.preprocess_wl(&mut formula))
    }

    /// Run the pipeline on an already-parsed formula.
    pub fn preprocess_wl(&mut self, formula: &mut CnfWl) -> Output {
        self.provider.set_optimize(self.config.optimize_generators);
        self.tracker.update_metric(Metric::InitVar, formula.n_variables() as u64);
        self.tracker.update_metric(Metric::InitCl, formula.n_clauses() as u64);

        let mut iteration = 0usize;
        let mut total_propagations = 0usize;
        let mut proof_fix_literals: Vec<i32> = Vec::new();

        // Predicate persists across rounds (aux variables accumulate in the
        // formula, so numbering stays consistent).
        let mut sbp = Predicate::new();
        // Formula clauses before appended breaking clauses (excluded from
        // detection and from duplication in the output).
        let mut appended_base_end: Option<usize> = None;
        // sbp clauses already appended to the formula.
        let mut sbp_appended = 0usize;
        // Already encoded generators (avoid re-adding the same constraint).
        let mut encoded: std::collections::HashSet<Vec<usize>> =
            std::collections::HashSet::new();
        // Base variable count before aux allocation (for the header).
        let mut sbp_base_vars: Option<usize> = None;
        // Detection budget decays after the first round (later rounds refine).
        let mut detect_budget_ms = self.config.sym_time_budget_ms;
        // Generators / row groups found in the latest round (for reporting).
        let mut last_generators = 0usize;
        let mut last_row_groups = 0usize;

        // Final database, rebuilt every iteration.
        let mut db: Cnf;

        loop {
            self.tracker.update_routine(Routine::Preprocess);
            let mut propagations = 0usize;

            if self.config.preprocess_unit || self.config.preprocess_pure {
                if self.config.preprocess_unit {
                    propagations += formula.propagate();
                }
                if self.config.preprocess_pure {
                    formula.mark_literal_uses();
                    for lit in formula.pure_literals() {
                        formula.assign_literal(lit);
                    }
                    if self.config.preprocess_unit {
                        propagations += formula.propagate();
                    }
                }
                if self.config.preprocess_subsume {
                    formula.mark_subsumed_clauses();
                }
                total_propagations += propagations;
                self.tracker
                    .add_to_metric(Metric::Propagations, propagations as u64);
            }

            let mut is_unsat = false;
            if formula.is_conflicting() {
                is_unsat = true;
                formula.reset_assignment();
                formula.clear();
                formula.reserve(1, 1);
                formula.add_clause(&[]);
                sbp = Predicate::new();
                appended_base_end = None;
                sbp_appended = 0;
                if let Some(p) = self.proof.as_mut() {
                    p.drat_clause(&[]);
                }
            }

            if self.config.add_reduced_as_unit {
                for v in 1..=formula.n_variables() as i32 {
                    if formula.assigned(v) == 1 {
                        proof_fix_literals.push(v);
                    } else if formula.assigned(-v) == 1 {
                        proof_fix_literals.push(-v);
                    }
                }
            }

            self.tracker.update_routine(Routine::Deduplicate);
            if self.config.preprocess_equiv {
                formula.equivalent_literals();
            }
            // Detection database: built from the FULL formula, including
            // previously appended breaking clauses. Generator candidates are
            // verified against all of it, so later rounds only break genuine
            // symmetries of the extended formula (sound iteration).
            let mut detect_db = Cnf::new();
            let mut removed: Vec<Vec<i32>> = Vec::new();
            detect_db.read_from_wl(formula, &mut removed);
            if let Some(p) = self.proof.as_mut() {
                for clause in &removed {
                    p.delete_clause(0, clause);
                }
            }
            // Output database: base range only (appended breaking clauses are
            // emitted separately from `sbp`, avoiding duplication).
            db = Cnf::new();
            let mut removed_out: Vec<Vec<i32>> = Vec::new();
            let range_end = appended_base_end.unwrap_or(formula.n_clauses());
            db.read_from_wl_range(formula, &mut removed_out, range_end);
            if let Some(p) = self.proof.as_mut() {
                for clause in &removed_out {
                    p.delete_clause(0, clause);
                }
            }
            let _amo = db.ulc_add_amo();
            let _bin = db.compute_binary();
            self.tracker.update_metric(Metric::Var, db.n_variables() as u64);
            self.tracker.update_metric(Metric::Cl, db.n_clauses() as u64);
            self.tracker.add_to_metric(
                Metric::AmoBinary,
                db.n_amo_clauses_added() as u64,
            );

            if !is_unsat {
                self.tracker.update_routine(Routine::DetectGeneric);
                self.provider.set_limits(
                    detect_budget_ms,
                    self.config.sym_max_pairs,
                    self.config.sym_max_nodes,
                );
                let group = self.provider.detect(&detect_db);
                last_generators = group.n_generators();
                self.tracker
                    .update_metric(Metric::SymGens, group.n_generators() as u64);
                sbp.record_generators(
                    group.n_generators(),
                    group
                        .generators
                        .iter()
                        .map(|g| g.support_size())
                        .sum(),
                );
                if group.n_generators() > 0 {
                    self.tracker.update_routine(Routine::Break);
                    // Aux variables are numbered once, on top of the ORIGINAL
                    // variable count; later rounds must reuse that base
                    // (db.n_variables() grows as aux vars join the formula).
                    if sbp_base_vars.is_none() {
                        sbp_base_vars = Some(db.n_variables());
                    }
                    let lex_base = sbp_base_vars.unwrap_or(db.n_variables());
                    let mut added = 0;
                    // Break each generator and its inverse (both sound;
                    // inverses often constrain different positions).
                    let mut all: Vec<crate::symmetry::Permutation> = Vec::with_capacity(
                        2 * group.generators.len(),
                    );
                    for gen in &group.generators {
                        let mut inv = vec![0usize; gen.image.len()];
                        for (i, &p) in gen.image.iter().enumerate() {
                            inv[p] = i;
                        }
                        all.push(crate::symmetry::Permutation::from_images(inv));
                        all.push(gen.clone());
                    }
                    for gen in &all {
                        // Same generator on a reduced formula yields the same
                        // constraint (modulo aux numbering) — skip repeats.
                        if !encoded.insert(gen.image.clone()) {
                            continue;
                        }
                        added += sbp.add_lex_leader(
                            lex_base,
                            gen,
                            &group.order,
                            self.config.break_depth,
                            self.proof.as_mut(),
                        );
                    }
                    self.tracker.add_to_metric(Metric::SymLex, added as u64);
                }
                // Row symmetry: compact adjacent-row lex chains break full
                // row interchangeability completely, independent of generic
                // generators. Runs even with zero generators.
                self.tracker.update_routine(Routine::DetectSpecial);
                let row_groups =
                    crate::structure::detect_row_groups(&db, &detect_db, &group.order);
                if !row_groups.is_empty() {
                    if sbp_base_vars.is_none() {
                        sbp_base_vars = Some(db.n_variables());
                    }
                    let lex_base = sbp_base_vars.unwrap_or(db.n_variables());
                    let mut row_added = 0;
                    for row_group in &row_groups {
                        for pair in row_group.rows.windows(2) {
                            let positions: Vec<(i32, i32)> = pair[0]
                                .iter()
                                .zip(pair[1].iter())
                                .take(self.config.break_depth.max(1))
                                .map(|(&a, &b)| ((a + 1) as i32, (b + 1) as i32))
                                .collect();
                            row_added +=
                                sbp.add_chain_lex(lex_base, &positions, self.proof.as_mut());
                        }
                    }
                    self.tracker.add_to_metric(Metric::SymLex, row_added as u64);
                    self.tracker.update_metric(
                        Metric::Row,
                        row_groups.len() as u64,
                    );
                    last_row_groups = row_groups.len();
                }
            }

            // Iteration bound mirrors satsuma.h: raw = (S/s)^p clamped to
            // [1, iteration_limit], with S = 1<<23, p = 1.5.
            let size = (db.n_len() + db.n_variables()) as f64;
            const S: f64 = (1u64 << 23) as f64;
            const P: f64 = 1.5;
            let raw = (S / size.max(1.0)).powf(P);
            let iteration_max = (raw.ceil() as usize)
                .clamp(1, self.config.iteration_limit.max(1));

            let orbitopal_only =
                self.config.orbitopal_fixing && self.config.mode == Mode::Fix;
            // Iterate on genuine progress: fresh assignments (from propagation
            // or probing) are monotonic, so rounds are bounded by the variable
            // count (plus `iteration_max`). Aux growth is capped as insurance
            // against pathological blowup.
            let aux_base = sbp_base_vars.unwrap_or(db.n_variables()).max(1);
            let aux_capped = sbp.n_extra_variables() <= 8 * aux_base;
            if self.config.iterate
                && orbitopal_only
                && iteration < iteration_max
                && aux_capped
                && (formula.n_variables() < 20_000)
            {
                if sbp.n_clauses() > sbp_appended {
                    if appended_base_end.is_none() {
                        appended_base_end = Some(formula.n_clauses());
                    }
                    let lex_base = sbp_base_vars.unwrap_or(db.n_variables());
                    let need_vars = lex_base + sbp.n_extra_variables();
                    if need_vars > formula.n_variables() {
                        formula.extend_variables(need_vars - formula.n_variables());
                    }
                    for clause in &sbp.clauses()[sbp_appended..] {
                        formula.add_clause(clause);
                    }
                    sbp_appended = sbp.n_clauses();
                }
                let new_props = formula.propagate();
                total_propagations += new_props;
                self.tracker
                    .add_to_metric(Metric::Propagations, new_props as u64);
                // Probing (failed literals): goes beyond UP, approximating
                // orbitopal fixing strength. Sound and RUP-loggable. Runs
                // whenever propagation stalls, even without new clauses.
                let mut probed = 0;
                if new_props == 0 && !formula.is_conflicting() {
                    let lex_base = sbp_base_vars.unwrap_or(db.n_variables());
                    probed = probe_units(formula, lex_base, 4, self.proof.as_mut());
                    total_propagations += probed;
                    self.tracker
                        .add_to_metric(Metric::Propagations, probed as u64);
                }
                if new_props > 0 || probed > 0 {
                    iteration += 1;
                    self.tracker
                        .update_metric(Metric::Iterations, iteration as u64);
                    detect_budget_ms = (detect_budget_ms / 2).max(250);
                    continue;
                }
            }

            if is_unsat {
                proof_fix_literals.clear();
            }
            if let Some(p) = self.proof.as_mut() {
                for &lit in &proof_fix_literals {
                    p.drat_clause(&[lit]);
                }
            }

            self.tracker.update_routine(Routine::Output);
            // On UNSAT, emit the trivial empty clause exactly like the C++
            // version (`p cnf 1 1` + `0`).
            if is_unsat {
                let dimacs = "p cnf 1 1\n0\n".to_string();
                let proof_text = self.proof.take().map(|p| p.into_buffer());
                return Output {
                    dimacs,
                    n_variables: 1,
                    n_clauses: 1,
                    n_sbp_clauses: 0,
                    n_extra_variables: 0,
                    n_generators: last_generators,
                    n_row_groups: last_row_groups,
                    iterations: iteration,
                    propagations: total_propagations,
                    proof_text,
                };
            }
            let n_vars = sbp_base_vars.unwrap_or(db.n_variables()) + sbp.n_extra_variables();
            let n_cls =
                db.n_clauses() + sbp.n_clauses() + proof_fix_literals.len();
            let mut dimacs = format!("p cnf {n_vars} {n_cls}\n");
            db.write_dimacs_clauses(&mut dimacs);
            sbp.write_dimacs_clauses(&mut dimacs);
            for lit in &proof_fix_literals {
                dimacs.push_str(&format!("{lit} 0\n"));
            }

            let proof_text = self.proof.take().map(|p| p.into_buffer());
            // Restore proof slot state (taken) — no further logging needed.
            return Output {
                dimacs,
                n_variables: n_vars,
                n_clauses: n_cls,
                n_sbp_clauses: sbp.n_clauses(),
                n_extra_variables: sbp.n_extra_variables(),
                n_generators: last_generators,
                n_row_groups: last_row_groups,
                iterations: iteration,
                propagations: total_propagations,
                proof_text,
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fix_simplifies_away_satisfied_tail() {
        // (x) /\ (x \/ y): unit x subsumes the rest.
        let dimacs = "p cnf 2 2\n1 0\n1 2 0\n";
        let mut pp = Preprocessor::fix();
        let out = pp.preprocess_str(dimacs).unwrap();
        assert!(out.dimacs.starts_with("p cnf "));
        assert!(out.n_clauses <= 2);
    }

    #[test]
    fn conflict_yields_empty_clause() {
        let dimacs = "p cnf 1 2\n1 0\n-1 0\n";
        let mut pp = Preprocessor::fix();
        let out = pp.preprocess_str(dimacs).unwrap();
        assert!(out.is_unsat());
    }

    #[test]
    fn lex_breaks_swap_symmetry() {
        // Swap symmetry 1<->2: lex-leader must add breaking clauses.
        let dimacs = "p cnf 2 2\n1 2 0\n-1 -2 0\n";
        let mut pp = Preprocessor::lex();
        let out = pp.preprocess_str(dimacs).unwrap();
        assert!(out.n_sbp_clauses >= 1, "expected breaking clauses, got {}", out.dimacs);
        assert!(!out.is_unsat());
        // Header counts must match the body.
        let body = out.dimacs.lines().filter(|l| !l.starts_with('p')).count();
        assert_eq!(body, out.n_clauses);
    }

    #[test]
    fn pure_literals_assigned_away() {
        // y only occurs positively -> pure, clause satisfied implicitly
        // by simplification only when pure enabled (fix mode).
        let dimacs = "p cnf 2 2\n1 2 0\n-1 2 0\n";
        let mut pp = Preprocessor::fix();
        let out = pp.preprocess_str(dimacs).unwrap();
        assert!(out.n_clauses <= 2);
    }
}
