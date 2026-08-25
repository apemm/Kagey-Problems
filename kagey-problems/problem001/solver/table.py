"""Difference-set table + preprocessing. OWNER: Arjun.

Suggested interface:

def difference_table(rects) -> list[frozenset]:
    '''All pairwise symmetric differences of corner sets.'''

def prune(rows) -> list[frozenset]:
    '''Deduplicate; delete rows containing another row (PROBLEM.md convention 5).'''

Fixture: the pruned 2x4 table must be exactly the six column-pair rows (ledger.md).
"""

def difference_table(rects):
    raise NotImplementedError

def prune(rows):
    raise NotImplementedError
