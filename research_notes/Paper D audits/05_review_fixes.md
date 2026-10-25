# 05: fixes after the review of the October 25 updates

Date: 2026-10-25. This note records how we answered section D of the review of commit 66dc9c4
(reviewers DD1 and DD2). Folder: `kagey-problems/problem131/paperD`.

## 1. Signs of the zero run (moderate, DD2-F001)

The proof of Theorem 4.4 needs the 2 intervals of the zero run that cover [0.668, 0.6688] to be
negative and the 5 that cover [0.6692, 0.6712] to be positive. Neither the text nor `check` said so.

- Proof of `thm:threshold` (`app_threshold.tex`): it now states these signs, says that on
  [0.6688, 0.6692] the pieces up to z- are negative and those from z+ on positive, and that the
  script prints and checks the arrangement.
- Section S6 (`online_resource_body.tex`): new last subsection (`or:thr-runs`), "From the runs to
  the theorem". It lists the signs, explains why the order matters (a positive interval left of
  z- would give another zero and break parts (a) and (c)) and describes the checks.
- `sec_verify.tex`: the mode `check` now verifies the sign - on all of (1/2, z-] and + on all of
  [z+, 0.6712].
- `certify_threshold.py`:
  - each accepted line now ends in `sign=-`, `sign=+` or `sign=-0+` and `exact=[lo, hi]` with
    exact rationals;
  - mode `zero` prints the count of negative intervals left of the zero piece and positive ones
    right of it, and exits 1 with a FAIL line unless the signs are - then +;
  - mode `cover` exits 1 unless every interval has the wanted sign;
  - `check` parses every `ok` line. It requires sign - on every interval of the 7 scaled runs, a
    contiguous cover by those intervals, exactly one interval with pattern `-0+` that contains
    [z-, z+], sign - on every interval left of it and + on every interval right of it. Otherwise
    it prints FAIL and returns 1.
- Negative test: with one sign of the zero record flipped in memory, `check` printed
  "FAIL zero run: the signs are not - left of [z-, z+] and + right of it" and returned 1. On the
  true records it returns 0.

## 2. Asserts (minor, DD2-F002)

All 9 `assert` statements in the 4 scripts are gone (threshold_taylor.py 5, threshold_pointwise.py 3,
threshold_hankel.py 1, certify_threshold.py had none). They now call `require(cond, msg)`, defined in
`threshold_pointwise.py`, which raises ValueError. The driver catches only ValueError now (it caught
AssertionError too). As before, a failed check rejects the attempt and never accepts an interval.
`python -I -O -B certify_threshold.py check` and a `cover` run under `-O` both pass.

## 3. The remaining items of section D

- z+ (DD2-F003): `sec_bulk_applications.tex` now writes z+ = 0.668812860014601028... and, for
  symmetry, z- = 0.668812860014597754..., both truncated (checked with 30-digit decimals). The
  README uses the same digits.
- "Up to flat modal intervals" (DD1-F001): replaced by "unless g_a (or its density) is constant on
  some interval", which matches the last sentence of Theorem 4.2. Changed in the abstract, the
  introduction, after Theorem 4.4, in the cover letter and in the README. The sentence after the
  proof of Theorem 4.3 now says that such an interval could be a flat mode or a flat stretch away
  from the modes, and that we do not rule it out. We did not try to prove real-analyticity.
- Dependence on Theorem 4.3 (DD1-F002): the text after Theorem 4.4 now says that the certificate
  proves part (b) on all of [z+, 1) by itself, and that Theorem 4.3 gives a second, computer-free
  proof on [39/40, 1). The sentence before Theorem 4.4 no longer says that the certificate
  "covers the rest". It covers (1/2, 1) apart from an interval shorter than 3.3e-15.
- "we use this below" (DD1-F003): replaced by "Theorem 4.3 below uses neither result. It needs only
  the first two exact moments."

## 4. The rerun

Full certificate, `python -I -B certify_threshold.py full --out data/certify_threshold_output.txt`
(Python 3.14.3, python-flint 0.9.0, mpmath 1.3.0, 24 cores). All 9 processes exit 0. Wall time
1687 s. Process times 857, 549, 889, 1514, 1687, 1094, 1113 s (scaled), 767 s (zero), 1480 s
(Hankel), 9950 s or about 2.8 CPU hours. Every `ok` and Hankel box line agrees with the committed
records of the first run apart from the new sign and exact fields (same T2, N, prec, K, eta, G0,
eta = 1.04e-15 on [0.6688, 0.6692], 115 boxes with H0, k <= 56). The records `data/threshold_*.txt`
carry the new sha256 header:

- certify_threshold.py 2824c6fe018e201cf2b21f6e067a3785bae4e85ff36f0296f6db5521f8762e73
- threshold_taylor.py d7489969a2e124cd0184b1491f5993d2b7aa3dfb1f86eec31cc321376b5c6d2c
- threshold_pointwise.py 0c581ba9ed8f7bff0fe204edecd1e76cd6696d931a6edfdbd9f2be98059b87bd
- threshold_hankel.py 26cada2559cc7dc36d869d5b55d1dcaa10961cb3f1c6b8cdec617e8f6ae4731c

The times in the paper changed accordingly: Table 2 has 13 min for the zero run (was 12),
the Code availability paragraph says about 2.8 hours or 28 minutes in 9 processes (was 2.7 and 29),
Remark 4.5 says about 2.8 hours. The README section on certificate runs describes both runs.

`py -I verify_all.py --quick`: all 6 scripts pass in 5.7 minutes, output in
`data/verify_output_2026-10-25_review.txt`. The quick mode of `certify_threshold.py` took 114 s and
both reruns match the records, sign fields included.

## 5. Builds

Journal build 45 pages, arXiv build 64 pages, both with no undefined or multiply defined
references and no overfull boxes. Aux files and `__pycache__` deleted, PDFs kept. Nothing in
`lean/` changed.
