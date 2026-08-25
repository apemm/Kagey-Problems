"""Rectangle enumeration. OWNER: Arjun.

Suggested interface (edit freely; you own the architecture):

def rectangles(rows: int, cols: int) -> list[frozenset[tuple[int, int]]]:
    '''All rectangles with four corners on grid points, tilted included,
    degenerates excluded, deduplicated. Points are (i, j) = (column, row),
    1-indexed, per PROBLEM.md convention 1.'''

Validation gate before anything downstream trusts this module:
hand-check counts on 2x3 (should be 3) and 3x3 (axis-aligned + tilted; count by hand first).
"""

def rectangles(rows, cols):
    raise NotImplementedError
