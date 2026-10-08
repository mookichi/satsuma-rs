//! Lightweight run statistics.
//!
//! Mirrors `tracker.h` minus the console table formatting: counters for the
//! pipeline stages plus per-routine wall-clock time.

use std::time::Instant;

/// Pipeline stages, mirroring `profiler_token` in `utility.h`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Routine {
    DetectGeneric,
    DetectSpecial,
    Preprocess,
    Parse,
    Hypergraph,
    Refine,
    Schreier,
    Optimize,
    Order,
    Break,
    Deduplicate,
    Output,
    Other,
}

impl Routine {
    pub fn name(self) -> &'static str {
        match self {
            Routine::DetectGeneric => "dejavu",
            Routine::DetectSpecial => "structure",
            Routine::Preprocess => "simplify",
            Routine::Parse => "parse",
            Routine::Hypergraph => "hypergraph",
            Routine::Refine => "refine",
            Routine::Schreier => "schreier",
            Routine::Optimize => "optimize",
            Routine::Order => "order",
            Routine::Break => "break",
            Routine::Deduplicate => "deduplicate",
            Routine::Output => "output",
            Routine::Other => "other",
        }
    }
}

/// Counters collected during preprocessing, mirroring `tracker_metrics`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Metric {
    CostSym,
    InitVar,
    InitCl,
    Var,
    Cl,
    SymUnit,
    SymBinary,
    SymLex,
    SymGens,
    Johnson,
    Row,
    RowColumn,
    Iterations,
    Propagations,
    AmoBinary,
}

const N_METRICS: usize = 15;

fn metric_index(m: Metric) -> usize {
    match m {
        Metric::CostSym => 0,
        Metric::InitVar => 1,
        Metric::InitCl => 2,
        Metric::Var => 3,
        Metric::Cl => 4,
        Metric::SymUnit => 5,
        Metric::SymBinary => 6,
        Metric::SymLex => 7,
        Metric::SymGens => 8,
        Metric::Johnson => 9,
        Metric::Row => 10,
        Metric::RowColumn => 11,
        Metric::Iterations => 12,
        Metric::Propagations => 13,
        Metric::AmoBinary => 14,
    }
}

/// Run statistics collector.
#[derive(Debug)]
pub struct Tracker {
    metrics: [u64; N_METRICS],
    time_by_routine: [f64; 13],
    current: Routine,
    last: Instant,
    start: Instant,
    /// When true, all console output is suppressed.
    pub silent: bool,
}

impl Default for Tracker {
    fn default() -> Self {
        let now = Instant::now();
        Self {
            metrics: [0; N_METRICS],
            time_by_routine: [0.0; 13],
            current: Routine::Parse,
            last: now,
            start: now,
            silent: true,
        }
    }
}

impl Tracker {
    pub fn new() -> Self {
        Self::default()
    }

    fn routine_index(r: Routine) -> usize {
        match r {
            Routine::DetectGeneric => 0,
            Routine::DetectSpecial => 1,
            Routine::Preprocess => 2,
            Routine::Parse => 3,
            Routine::Hypergraph => 4,
            Routine::Refine => 5,
            Routine::Schreier => 6,
            Routine::Optimize => 7,
            Routine::Order => 8,
            Routine::Break => 9,
            Routine::Deduplicate => 10,
            Routine::Output => 11,
            Routine::Other => 12,
        }
    }

    /// Switch the current routine, attributing elapsed time to the previous one.
    pub fn update_routine(&mut self, routine: Routine) {
        let now = Instant::now();
        let dt = (now - self.last).as_secs_f64() * 1000.0;
        self.time_by_routine[Self::routine_index(self.current)] += dt;
        self.current = routine;
        self.last = now;
    }

    pub fn add_to_metric(&mut self, metric: Metric, value: u64) {
        self.metrics[metric_index(metric)] =
            self.metrics[metric_index(metric)].saturating_add(value);
    }

    pub fn update_metric(&mut self, metric: Metric, value: u64) {
        self.metrics[metric_index(metric)] = value;
    }

    pub fn get(&self, metric: Metric) -> u64 {
        self.metrics[metric_index(metric)]
    }

    /// Total elapsed wall-clock time in milliseconds.
    pub fn elapsed_ms(&self) -> f64 {
        (Instant::now() - self.start).as_secs_f64() * 1000.0
    }

    /// One-line `c ...` summary, in the style of the original.
    pub fn summary(&self) -> String {
        format!(
            "c [vars {} clauses {} sym_gens {} sym_lex {} propagations {} iterations {}]",
            self.get(Metric::Var),
            self.get(Metric::Cl),
            self.get(Metric::SymGens),
            self.get(Metric::SymLex),
            self.get(Metric::Propagations),
            self.get(Metric::Iterations),
        )
    }
}
