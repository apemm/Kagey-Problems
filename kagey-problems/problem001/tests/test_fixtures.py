"""Tests written first, from the hand-verified ledger. They fail until the engine exists."""
import pytest
from solver.engine import max_blackout

# (rows, cols, max_blackout, witness_count) — hand-proved entries only
CASES = [
    (2, 2, 4, 1),
    (2, 3, 4, 12),
    (2, 4, 5, 32),
]

# Pre-registered 2026-08-24; promote to CASES only after the engine confirms it
PREDICTIONS = [
    (2, 5, 6, 80),
]

@pytest.mark.parametrize("rows,cols,value,witnesses", CASES)
def test_ledger(rows, cols, value, witnesses):
    v, w = max_blackout(rows, cols)
    assert (v, w) == (value, witnesses)

@pytest.mark.parametrize("rows,cols,value,witnesses", PREDICTIONS)
def test_strip_theorem_prediction(rows, cols, value, witnesses):
    v, w = max_blackout(rows, cols)
    assert (v, w) == (value, witnesses)

@pytest.mark.parametrize("m", range(3, 8))
def test_strip_formula(m):
    v, w = max_blackout(2, m)
    assert (v, w) == (m + 1, m * 2 ** (m - 1))

def test_brute_agreement():
    from solver.brute import max_blackout_brute
    for rows, cols in [(2, 2), (2, 3), (2, 4), (3, 3)]:
        assert max_blackout(rows, cols) == max_blackout_brute(rows, cols)[:2]


@pytest.mark.parametrize("rows,cols,n", [(2, 3, 3), (3, 3, 10), (3, 4, 20)])
def test_rectangle_counts(rows, cols, n):
    from solver.enumerate import rectangles
    assert len(rectangles(rows, cols)) == n


def test_pruned_2x4_is_column_pairs():
    from solver.enumerate import rectangles
    from solver.table import difference_table, prune
    pruned = prune(difference_table(rectangles(2, 4)))
    cols = {frozenset({(i, 1), (i, 2), (k, 1), (k, 2)}) for i in range(1, 5) for k in range(i + 1, 5)}
    assert set(pruned) == cols and len(pruned) == 6
