# 04: the threshold certificate in Paper D

Date: 2026-10-25. This note records how the audited certificate of
`research_notes/Paper D threshold certificate/` (reports 01 and 02, audit 03) entered
`kagey-problems/problem131/paperD`.

## What the paper now states

Theorem 4.4 (`thm:threshold`, `sec_bulk_applications.tex`) is computer-assisted. It uses
z- = 1838418790980431/2748779069440000 = 0.66881286001459775... and
z+ = 45960469774511/68719476736000 = 0.66881286001460103..., with z+ - z- = 3.27e-15.

- (a) g_a''(0) < 0 and case (a) of Theorem 4.2 for every a in (1/2, z-];
- (b) case (b) for every a in [z+, 1), and g_a''(0) > 0 on [z+, 0.6712];
- (c) a -> g_a''(0) has a zero in (z-, z+), and every zero in (1/2, 0.6712] lies there.

The text after it says that the supremum of the a with case (a) and the infimum of the a with
case (b) lie in [z-, z+], that uniqueness of the zero and the case inside (z-, z+) are open,
that Theorem 4.3 stays as the computer-free result for a >= 39/40 and that the certificate
covers the rest. Remark 4.4 became Remark 4.5 (`rem:modes-threshold`, label kept). It sketches
the method and keeps the finite-N values 0.6563 and 0.6592.

## Where the proofs went

The journal build with full proofs in Appendix G came to 48 pages. So the proofs were split as follows.

- Appendix G (`app_threshold.tex`, both builds) states the four steps, proves the Hankel test
  (Lemma G.1) and proves Theorem 4.4 from the runs, with Table 2 of the runs.
- Section S6 of the arXiv version (end of `online_resource_body.tex`, label `or:threshold`)
  holds Lemmas S6.1 to S6.8 with full proofs: the moment bounds (01 Lemma 1 and 02 Lemma 6),
  truncation (01 Lemma 2), Taylor cells (01 Lemma 3), the tail (01 Lemma 4, with T3 >= 2^a T2 as
  in 02 Lemma 8), the formula for g''(0) (01 Lemma 5), the Cauchy remainder (02 Lemma 7), the
  enclosure on an interval (02 Lemma 8 and Theorem A) and the scaled variable (02 Lemma 9).
- The sentences that said every proof is in the article (introduction, Data availability,
  cover letter) now name this exception.

Page counts: journal 45 pages (limit 45), arXiv 64 pages.

## Code

- `certify_threshold.py` is the driver (from `certify_interval.py` and the driver part of
  `hankel_certify.py`), with modes `scaled`, `zero`, `cover`, `hankel`, `full`, `check`, `quick`
  and an `--out FILE` option that writes the sha256 header and the exit line.
- `threshold_taylor.py` is `erw_tm.py`, `threshold_pointwise.py` is `erw_cf.py`, and
  `threshold_hankel.py` is the rest of `hankel_certify.py`. The computational code is unchanged
  (checked by diff). Only docstrings, comments and imports changed, and the unused
  `moments_ball` and `check_box` were dropped.
- The guard asked for by audit 03, Remark 2, is in `threshold_hankel.check_box_tm`,
  `assert qq < 1` right after `qq = w / rho`.
- `verify_all.py` runs `certify_threshold.py quick` by default and `certify_threshold.py full`
  under `--full`. `verify_elephant_modes.py` changed only in labels (Remark 4.4 -> 4.5, the grid
  part is now a cross-check of Theorem 4.4).

## The full run

`python -I -B certify_threshold.py full --out data/certify_threshold_output.txt` in `paperD`
(Python 3.14.3, python-flint 0.9.0, mpmath 1.3.0, 24 cores). 9 processes, all exit 0, wall time
1711 s. Process times 826, 538, 853, 1524, 1711, 1058, 1072 s (the 7 scaled ranges), 741 s
(zero run) and 1493 s (Hankel), about 2.7 CPU hours. Records in `paperD/data/threshold_*.txt`
with the sha256 header of the 4 scripts and the exit line. `check` confirms the cover of
(1/2, 1) and the undecided piece exactly [z-, z+]. The zero run reproduces the stored line of 02
(eta = 1.04e-15 on [0.6688, 0.6692]). The Hankel run uses H0 on all 115 boxes, orders k <= 56,
remainders below 1.6e-28.

`py -I verify_all.py --quick` in `paperD` passes all 6 scripts in 5.9 minutes
(`paperD/data/verify_output_2026-10-25_threshold.txt`). The quick mode of
`certify_threshold.py` takes 118 s. It reruns the first scaled interval (N = 1400, prec = 1335,
the same eta = 0.0768 and G0 = -0.398726 as audit 03) and [0.6704, 0.6708], and both match the
records.

The stale record `interval_scaled_0.50_0.53.txt` (N = 1200, prec = 900, audit 03 Remark 1) is
replaced by `paperD/data/threshold_scaled_0.50_0.53.txt`, made by the current code.

## Wording fix for 01_report.md (not in the paper)

Audit 03, Remark 3: the Corollary of 01, Section 3, says "a third maximum is excluded", which is
informal. The correct inference is that of 02, Section 0. Replace the Corollary by the text below.

> Corollary (modality). g_a''(0) = f_a''(0), and g_a is C^2 and even, so g_a'(0) = 0. If
> f_a''(0) < 0, then g_a' < 0 on some (0, delta), which contradicts case (b) of Theorem 4.2,
> where g_a is nondecreasing on [0, c]. So case (a) holds. If f_a''(0) > 0, then g_a' > 0 on
> some (0, delta), which contradicts case (a), where g_a is nonincreasing on [0, oo). So case
> (b) holds. Plateaus elsewhere do not matter.

01_report.md itself was left unchanged, since it is outside the write scope of this pass.

## Open items for the author

- The Code availability pin (commit 6f7f9068) predates the certificate. The paper says the
  certificate is newer. Replace the pin by a checked commit once the files are committed.
- GLR is cited as the AIHP version (`glr2026`), but Theorem 1.1, (2.10), Theorem 2.5 (Step 4)
  and Corollary 2.11 were checked against arXiv:2308.14630v2. Confirm the numbering in the
  journal version.
- Khinchine's theorem is cited to Dharmadhikari and Joag-dev (1988), with no section number, and the Arb
  paper (Johansson 2017) is new in the bibliography. Check both entries.
