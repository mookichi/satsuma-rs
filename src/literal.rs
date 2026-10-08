//! Literal <-> graph-vertex mappings.
//!
//! Mirrors `utility.h`: SAT literals are mapped to dense graph vertices
//! `v = 2*(|l|-1) + (l<0)` so that positive and negative literals of one
//! variable occupy adjacent vertices. The symmetry engine acts on these
//! vertices; the negation structure (`graph_negate`) must be preserved.

/// Maps a SAT literal to its graph vertex.
///
/// `l != 0` must hold; variable indices are 1-based.
#[inline]
pub fn sat_to_graph(l: i32) -> usize {
    debug_assert!(l != 0);
    (((l.abs() - 1) as usize) << 1) + usize::from(l < 0)
}

/// Maps a graph vertex back to its SAT literal.
#[inline]
pub fn graph_to_sat(vertex: usize) -> i32 {
    let is_neg = vertex & 1 == 1;
    let variable = (vertex >> 1) as i32 + 1;
    if is_neg {
        -variable
    } else {
        variable
    }
}

/// "Negates" a graph vertex, i.e. maps the vertex of `l` to the vertex of `-l`.
#[inline]
pub fn graph_negate(vertex: usize) -> usize {
    sat_to_graph(-graph_to_sat(vertex))
}

/// Variable index (0-based) of a literal.
#[inline]
pub fn var_index(lit: i32) -> usize {
    (lit.abs() - 1) as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        for l in [-10, -2, -1, 1, 2, 10] {
            assert_eq!(graph_to_sat(sat_to_graph(l)), l);
        }
    }

    #[test]
    fn negate() {
        for l in [-5, -1, 1, 5] {
            assert_eq!(graph_negate(sat_to_graph(l)), sat_to_graph(-l));
        }
    }
}
