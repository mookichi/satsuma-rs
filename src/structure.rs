//! Row symmetry detection and compact row breaking.
//!
//! If variables form a matrix whose rows are freely interchangeable (every
//! row swap preserves the formula), adjacent-row lex chains break the full
//! row symmetry completely with `(rows-1)` chains instead of one chain per
//! generator. Candidates come from long clauses; every row swap is verified
//! exactly, so wrong candidates only cost time, never soundness.

use crate::cnf::Cnf;
use crate::literal::{graph_to_sat, sat_to_graph};
use std::collections::HashSet;

/// Minimum row width considered (smaller rows stay with generic breaking).
pub const MIN_ROW_WIDTH: usize = 3;
/// Max candidates kept per row size (bounds detection work).
const MAX_CANDIDATES_PER_SIZE: usize = 256;
/// Max row-swap verification tests per detection call.
const MAX_SWAP_TESTS: usize = 4096;

/// A set of pairwise-interchangeable rows, aligned: `rows[i][j]` corresponds
/// to `rows[0][j]` via a verified row swap. Variable ids are 0-based.
#[derive(Debug, Clone)]
pub struct RowGroup {
    pub rows: Vec<Vec<usize>>,
}

/// Build the literal image swapping rows `a` and `b` elementwise
/// (positive↔positive, hence negations↔negations). Returns `None` when the
/// rows have different sizes.
fn row_swap_image(n_literals: usize, a: &[usize], b: &[usize]) -> Option<Vec<usize>> {
    if a.len() != b.len() {
        return None;
    }
    let mut image: Vec<usize> = (0..n_literals).collect();
    for (&x, &y) in a.iter().zip(b.iter()) {
        if x == y {
            continue;
        }
        let gx = sat_to_graph((x + 1) as i32);
        let gy = sat_to_graph((y + 1) as i32);
        let nx = crate::literal::graph_negate(gx);
        let ny = crate::literal::graph_negate(gy);
        image.swap(gx, gy);
        image.swap(nx, ny);
    }
    Some(image)
}

/// Detect row groups: `db` supplies candidates (long clauses), `full_db` is
/// used for exact swap verification (it sees appended breaking clauses too).
/// `order` gives the preferred variable sequence for the reference row.
pub fn detect_row_groups(db: &Cnf, full_db: &Cnf, order: &[usize]) -> Vec<RowGroup> {
    // Candidates: sorted variable sets of long clauses, grouped by size.
    let mut by_size: std::collections::BTreeMap<usize, Vec<Vec<usize>>> =
        std::collections::BTreeMap::new();
    let mut seen_candidates: HashSet<Vec<usize>> = HashSet::new();
    for c in db.clauses_iter() {
        if c.len() < MIN_ROW_WIDTH {
            continue;
        }
        let mut vars: Vec<usize> = c.iter().map(|&l| (l.abs() - 1) as usize).collect();
        vars.sort_unstable();
        vars.dedup();
        if vars.len() < MIN_ROW_WIDTH {
            continue;
        }
        if !seen_candidates.insert(vars.clone()) {
            continue;
        }
        let entry = by_size.entry(vars.len()).or_default();
        if entry.len() < MAX_CANDIDATES_PER_SIZE {
            entry.push(vars);
        }
    }

    let n_literals = 2 * db.n_variables();
    let mut groups: Vec<RowGroup> = Vec::new();
    let mut swap_tests = 0;
    let order_pos = |v: usize| order.iter().position(|&w| w == v).unwrap_or(usize::MAX);

    for (_, candidates) in by_size {
        // Greedy grouping: each candidate joins a group iff disjoint from and
        // pairwise-swappable with all its rows.
        'candidates: for cand in candidates {
            for group in groups.iter_mut().filter(|g| g.rows[0].len() == cand.len()) {
                if group.rows.iter().any(|r| r.iter().any(|v| cand.contains(v))) {
                    continue;
                }
                let mut aligned_ok = true;
                for row in &group.rows {
                    if swap_tests >= MAX_SWAP_TESTS {
                        return groups.into_iter().filter(|g| g.rows.len() >= 2).collect();
                    }
                    swap_tests += 1;
                    let image = match row_swap_image(n_literals, row, &cand) {
                        Some(img) => img,
                        None => {
                            aligned_ok = false;
                            break;
                        }
                    };
                    if !crate::automorphism::verify_automorphism(full_db, &image) {
                        aligned_ok = false;
                        break;
                    }
                }
                if aligned_ok {
                    // Align the candidate to the reference row via their swap.
                    let image = row_swap_image(n_literals, &group.rows[0], &cand)
                        .expect("same size, verified above");
                    let mut aligned = vec![0usize; cand.len()];
                    for (j, &x) in group.rows[0].iter().enumerate() {
                        let img_lit = graph_to_sat(image[sat_to_graph((x + 1) as i32)]);
                        aligned[j] = (img_lit.abs() - 1) as usize;
                    }
                    group.rows.push(aligned);
                    continue 'candidates;
                }
            }
            // Start a new group (may stay singleton → dropped later).
            let mut ref_row = cand.clone();
            ref_row.sort_by_key(|&v| order_pos(v));
            // Realignment of existing rows is unnecessary (single row).
            groups.push(RowGroup { rows: vec![ref_row] });
        }
    }
    groups.into_iter().filter(|g| g.rows.len() >= 2).collect()
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

    /// 2 pigeons x 3 holes: rows {1,2,3} and {4,5,6}.
    fn php_2x3() -> Cnf {
        db_of(
            &[
                vec![1, 2, 3],
                vec![4, 5, 6],
                vec![-1, -4],
                vec![-2, -5],
                vec![-3, -6],
            ],
            6,
        )
    }

    #[test]
    fn finds_pigeon_rows() {
        let db = php_2x3();
        let order: Vec<usize> = (0..6).collect();
        let groups = detect_row_groups(&db, &db, &order);
        assert_eq!(groups.len(), 1, "expected one row group, got {groups:?}");
        assert_eq!(groups[0].rows.len(), 2);
        let mut r0 = groups[0].rows[0].clone();
        let mut r1 = groups[0].rows[1].clone();
        r0.sort_unstable();
        r1.sort_unstable();
        assert!((r0 == vec![0, 1, 2] && r1 == vec![3, 4, 5])
            || (r0 == vec![3, 4, 5] && r1 == vec![0, 1, 2]));
    }

    #[test]
    fn rigid_formula_has_no_rows() {
        let db = db_of(&[vec![1], vec![1, 2]], 2);
        let order: Vec<usize> = (0..2).collect();
        assert!(detect_row_groups(&db, &db, &order).is_empty());
    }

    #[test]
    fn triangle_clauses_are_not_rows() {
        // Ramsey-style triangles share variables; no disjoint swappable pair.
        let db = db_of(
            &[
                vec![-1, -2, 3],
                vec![-1, -3, 2],
                vec![-2, -3, 1],
            ],
            3,
        );
        let order: Vec<usize> = (0..3).collect();
        assert!(detect_row_groups(&db, &db, &order).is_empty());
    }
}
