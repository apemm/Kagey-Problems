"""Minimum hitting set -> maximum blackout. OWNER: Arjun.

Suggested interface:

def max_blackout(rows: int, cols: int, count_witnesses: bool = True) -> tuple[int, int]:
    '''Returns (max blackout size, number of maximum blackouts).
    Pipeline: enumerate -> difference_table -> prune -> min hitting set (PuLP ILP);
    witness count by enumeration at small sizes.'''
"""

def max_blackout(rows, cols, count_witnesses=True):
    raise NotImplementedError
