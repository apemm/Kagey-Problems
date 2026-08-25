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
        assert max_blackout(rows, cols)[0] == max_blackout_brute(rows, cols)
