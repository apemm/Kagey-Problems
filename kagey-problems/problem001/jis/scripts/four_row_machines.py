"""Shared loader for the three exported four-row geometry machines.

Each machine file describes a deterministic filter for one row partition of the
four rows (zero-based rows in the file names: 01|23, 02|13, 03|12).  Letters are
column masks, bit 2^r meaning that row r is black: four singleton letters
1, 2, 4, 8 and the four double letters of the partition.  transitions[s][k] is the
state reached from state s on letter alphabet[k], or -1 for rejection.  State 0 is
the empty prefix, and every listed state is accepting for the geometry filter;
the product with the register of used doubles (each used exactly once) recognises
exactly the maximum blackouts of the 4 x m grid for m >= 6.

Rows are translated to one-based (column, row) coordinates only when a witness is
written out.
"""
import json
import os

ARCHIVE = os.environ.get(
    "PROBLEM001_ARCHIVE",
    r"C:\Users\arjun\Downloads\Problem 001 Research 2026-10-16\research_notes"
    r"\Problem 001 structural improvements\four_row")

MACHINES = [
    ("01|23", "machine_56910.json"),
    ("02|13", "machine_36912.json"),
    ("03|12", "machine_351012.json"),
]

SINGLETONS = (1, 2, 4, 8)


def partition_rows_one_based(name):
    """'01|23' -> '{1,2}|{3,4}' in one-based row labels."""
    a, b = name.split("|")
    return "{%s}|{%s}" % (",".join(str(int(c) + 1) for c in a),
                          ",".join(str(int(c) + 1) for c in b))


def load_machine(filename):
    with open(os.path.join(ARCHIVE, filename)) as f:
        d = json.load(f)
    alphabet = d["alphabet"]
    edges = d["edges"]
    assert alphabet[:4] == list(SINGLETONS)
    assert sorted(alphabet[4:]) == sorted(edges)
    for e in edges:
        assert bin(e).count("1") == 2
    n = d["state_count"]
    trans = d["transitions"]
    assert len(trans) == n and all(len(row) == 8 for row in trans)
    assert all(-1 <= t < n for row in trans for t in row)
    return {
        "alphabet": alphabet,
        "edges": edges,
        "transitions": trans,
        "state_count": n,
        "file": filename,
    }


def load_all():
    return [(name, load_machine(fn)) for name, fn in MACHINES]
