# Paper A: computational manifest

This file lists every computation behind the paper, what it produces and how to rerun it. The
per-script descriptions are in `../SUPPLEMENT.md`, and the statement-by-statement Lean coverage is
in `../lean/PaperA/MAP.md`.

## Environment

- Python 3.10 or later (last run with 3.14.3).
- The verification scripts use only the standard library, except `verify_ising_coupling_tm.py`,
  which needs NumPy (last run with 2.4.2).
- The figure scripts need NumPy, Matplotlib (last run with 3.10.8) and mpmath (1.3.0, for
  `figures/make_figures.py`), and the shared style `../figures/series_style.py`.
- Lean 4.33.1 with Mathlib v4.33.1 for the formal proofs (see `../lean/README.md`). Do not build
  Lean inside a synced folder such as OneDrive.

## Commands

Run everything from this folder (`paperA`).

| Command | Time | What it does |
| --- | --- | --- |
| `python -B verify_all.py` (same as `--quick`) | about 4 min | All checks except the 2 long certificate sweeps. Reads the stored certificates in `data/`. |
| `python -B verify_all.py --full` | about 25 min | Also reruns `verify_every_n.py` (rewrites `data/every_n_certificates.csv` and `data/every_n_output.txt`) and `verify_every_n_sign.py`. |
| `python -B verify_certified_bounds.py` | seconds | Replays the short-chain certificates (N <= 174), the 999 stored brackets and the sign range of Remark 3.9 with outward error bounds, from the stored rational endpoints. Also part of `verify_all.py`. |
| `python -B figures/make_figures.py` | seconds | Figures 1 to 5, and their data in `data/figures/`. |
| `python -B figures/make_coupling_figure.py` | seconds | Figure 6 and its data. |
| `python -B verify_all.py --paper a` (from `..`) | about 4 min | The same quick run through the series runner. |

Several scripts rewrite their recorded output in `data/`. Some of those files record run times, so
a rerun changes them without changing any checked value.

## What each table and figure comes from

| In the paper | Source | Method |
| --- | --- | --- |
| Table 1 (z_N against Theorem 3.4) | `verify_every_n.py` | run-count bisection at 50 digits and a floating-point dynamic program |
| Table 2 (couplings) | `verify_ising_coupling.py`, `verify_ising_coupling_tm.py` | run polynomials at 80 digits, and the transfer matrix in double precision (agree to 1e-12) |
| Figures 1 to 5 | `figures/make_figures.py` | run and cyclic polynomials, roots by bisection (tolerances in each JSON file) |
| Figure 6 | `figures/make_coupling_figure.py` | run and cyclic polynomials at 80 digits |
| Numbers in the text that no script prints | `data/quoted_values.txt` | listed with their method |

## Kinds of evidence

- **Exact certificates.** Integer evaluations of S_N at rational points for N <= 174 (Theorem 3.4,
  Proposition 3.8) and up to N = 2773 (Remark 3.9), each computed by two exact methods where stated.
- **Outward interval checks.** The comparisons of these certificates with zeta_N and its bounds,
  replayed by `verify_certified_bounds.py` with outward rounding.
- **Kernel-checked proofs.** The Lean theorems listed in `MAP.md`, including the certificates for
  N <= 174 with Lean's own rational bounds.
- **Sampled comparisons.** The asymptotic formulas against exact values at selected N (figures,
  Table 2, Proposition 5.7, Remark 5.8). These illustrate the theorems and are not part of any
  proof.
