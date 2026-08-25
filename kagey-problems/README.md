# Kagey Open Problems — Pemmasani

Work on problems from Peter Kagey's Open Problem Collection (peterkagey.com/problems).

- `problem001/` — grid blackouts preserving rectangle identifiability (in progress; strips solved)
- `problem137/` — the rational tree of x+1 and -1/x (complete solution; under author review)

**Disclosure.** Parts of this repository were developed with AI assistance (Claude, Anthropic).
All mathematics and all published numbers are verified by the authors: proofs are re-derived by
hand, and computations are cross-checked by two independently written implementations before
any value is recorded.

## Quickstart (problem 001)
```
pip install -r problem001/requirements.txt
cd problem001 && pytest          # tests are written first; they fail until the engine exists
```

## Roles
Engine architecture and implementation: Arjun Pemmasani.
Review, debugging, and a blind reimplementation used only for reconciliation: Claude.
Only values agreeing across both implementations enter the ledger, the paper, or correspondence.
