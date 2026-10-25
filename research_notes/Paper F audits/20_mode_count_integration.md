# 20. Integration of the exact mode count into Paper F (25 October 2026)

The sources are `research_notes/Paper F modes O1/04_report.md` (Theorem 1 and its proof), `05_report.md`
(Lemma 12 in full, the bell shape, (EQ)) and `06_audit.md` (the independent audit). The paper now
has 80 pages (63 before). The build is clean after three runs, with no undefined or multiply
defined references and no overfull boxes. The only warning is the class's `pagebackref` notice,
which was there before. `py -I verify_all.py --quick` passes all 6 scripts (1.1 min).

## What changed in the paper

1. **The conjecture is gone.** `conj:three-modes` and the paragraphs around it (end of Section 6.4)
   are replaced by a new Section 6.5, "The exact number of modes" (`sec:mode-count`).
2. **Theorem F** (`thm:mode-count`, an `introtheorem`, so the main theorems are now A to F). Under
   (SPAN), (LR), (LD2) for both signs and (EQ), for a fresh start of either sign or the fair start,
   with the no-tie condition at both ends, parts (i) to (v) give the full sign pattern of the first
   differences for all large N, and P_N has exactly `M_+ + M_- + 1` modes. The proof of the count
   from the sign pattern is in the main text, as a short argument on the sequence of signs.
3. **Corollaries and examples in Section 6.5.**
   - `cor:three-modes`. exactly three modes for all large N iff each end profile has exactly one
     local maximum.
   - `lem:one-max`. when the profile `(c_0, u(1), u(2), ...)` has one local maximum. (a) `u`
     nonincreasing on `j >= 1` is sufficient. (b) If `c_0 > u(1)` it is also necessary. (c) If
     `c_0 < u(1)` the local maxima are those of `(u(j))_{j>=1}`.
   - `cor:logconvex-three`. strictly log-convex run laws give exactly three modes for fresh starts,
     and for the fair start when `f_+(1)` and `f_-(1)` differ from 1/2. The zeta law is covered.
   - `cor:sequences`. Corollary 17 of 05, along the N with `min theta_N >= theta_0` and
     `alpha_+ = alpha_-`.
   - `ex:runs2`. every law with `f_+(1) = f_-(1) = 0` gives at least five modes for the fair start,
     by `lem:one-max`(b) and `thm:modes-lower`. For runs of length at least 2 with a power tail, a
     finite certified computation gives seven local maxima in each profile, so at least 15 modes
     for all large N. Exactly 15 follows from Theorem F if `u` decreases strictly on `[12, oo)`,
     which the computation confirms on `12 <= j <= 10^4`. The computed law has exactly 15 modes at
     every N = 2500, 2600, ..., 4000.
   - `lem:diff-bigjump`. the difference form of the local big jump (Lemma 8 of 04, D0 to D3 and the
     bound on `q_{m+1}`), stated in the main text as a lemma of independent interest. The paragraph
     after it positions it against Doney (1989), Denisov, Dieker and Shneer (2008, Theorem 9.1) and
     Berger (2019, Theorem 2.4). These give `f^{*m}(n)` up to a factor `1 + o(1)`, which says nothing
     about differences. The novelty claim is worded as "we do not know an earlier statement".
   - `rem:mode-open`. unequal scales (the bulk when theta -> 0, and the window of `thm:window`) and
     a bound for every N remain open. Parts (i) to (iii) hold without (EQ).
4. **Appendix B** (`sec_modeproofs.tex`, label `app:modes`) holds all the long proofs. Map from the
   notes to the labels:

   | Notes | Paper |
   |---|---|
   | 04 Lemma 2 | `lem:ld2` |
   | 04 Lemma 3 | `lem:second-renewal` |
   | 04 Lemma 4 (v) to (viii) | `lem:plus-second` (i) to (iv) |
   | 04 Theorem 5, §3.3 | `thm:layer-second` |
   | 04 Corollary 6, Theorem 7 | `cor:convex` and the proof of (iii) |
   | Fourier bound and truncated point masses used in 04 Lemma 8 | `lem:trunc-local` |
   | 04 Lemma 11 | `lem:fourier-diff` |
   | 04 Lemma 8 | proof of `lem:diff-bigjump` (Section B.4) |
   | 04 Theorem 10 | `thm:zone-diff` and the proof of (iv) |
   | 05 (F2), (F5), (F6) | displays `eq:right-tail`, `eq:left-local` and the line after |
   | 05 Lemma 12a | `lem:pointwise` |
   | 05 Lemma 12c | `lem:second-bigjump` |
   | 05 Lemma 12 (T2), (T1), (T1w) | `lem:tails` (a), (b), (c) |
   | 04 Lemma 13 and 05 Lemma 16 | `lem:bell` |
   | 04 Theorem 14 | `thm:bulk-diff` |
   | 04 Corollary 15 | `cor:bulk-sign` |
   | 04 §5.3 and the (EQ) discussion of 05 §3 | Section B.7 `app:junctions` |

   04 Theorem 1′ (no (EQ), outside two windows) is not in the paper. The audit found its
   bad-index estimate asserted in one sentence, and the paper says only that parts (i) to (iii)
   hold without (EQ), which the proofs show.
5. **Hypotheses.** (LD2) and (EQ) are added to the list in Section 2.2, with the remark that (LD2)
   implies (LD) under (LR) (`lem:ld2`) and that (EQ) forces equal indices.
6. **Abstract** (247 words, no theorem labels) and **introduction**. The abstract now states the
   exact count, the three-mode criterion, the log-convex case and the runs of length at least two.
   The introduction states Theorem F, the criterion, the failure of monotonicity as the criterion,
   the family `f(1) = 0`, the three steps of the proof and what stays open. The physics picture of a
   central peak between two side peaks (Zaburdaev, Denisov and Klafter) is now called exact on the
   lattice, with its criterion. The sentence "every theorem holds for every relation between the
   scales" now excludes Theorem F as well. Related work cites Doney (1989) and Kwaśnicki (2020).
   Two bibliography entries are new, `doney1989` and `kwasnicki2020`. Keywords add "number of modes"
   and "bell-shaped function".
7. **Section 7** reports the new computations.

## The audit's fixes

1. **Lemma 12c restricted to `L >= mu m`.** `lem:second-bigjump` assumes
   `L >= max(K_1 a(m), L_0, m mu)`. The no-giant part now uses `mT(delta L) <= C L^{1-alpha+eps}`,
   which gives a power of L and no factor `a(m)`. Every use satisfies the restriction. In
   `lem:tails`(a), range (i) has `m <= j/(2 mu)` and `L >= j/2`, and in (b) `m < m_eps` at a level
   of order N with `x - m mu >= x/2 >= m mu`.
2. **The junction.** Part (v) of Theorem F is stated on `|x_{N,k}| <= K_0 + 1`, and part (iv) on
   `j <= (1-p)N - K_0 B_N`, that is `x >= K_0`. So they overlap. `K_0` is also enlarged to be at least
   `R_0 = sup |x_theta|`, so that the bulk window contains every mode `x_theta`.
3. **The threshold w itself.** In `lem:plus-second`(i) (Lemma 4(v)) and in the second boundary term
   of `lem:second-bigjump` (Lemma 12c), the proof for the law `h_i` uses the threshold `w`, so a
   truncated variable is never a giant summand.
4. **The index slip in Lemma 3.** The second sum in the formula for `nabla(a*b)_n` ends at
   `n - M - 2`, and the boundary term is `a_{M+1} b_{n-M-1}`. I rederived the formula.

## Other points settled while writing the proofs

- **Lemma 8, step (1).** 04 asserted that the boundary term of the split is smaller. The paper
  bounds it by a two-block local bound for truncated sums, `lem:trunc-local`(a),
  `u^{(w)}_m(x) <= C a(m)^{-1} (mT(w))^{y/(4w)}` for deviations `y >= 2w`. This gives
  `C a(m)^{-2} (mT(w))^{L/(16w)}`, and the condition on delta becomes
  `(alpha - eps)/(32 delta) > alpha + 2 + eps`. The bound on `V_m(n)` (D0) uses the same lemma,
  which keeps the factor `1/a(m)` that a plain tail bound would lose.
- **The Fourier bound** `sup |nabla u^{(w)}_m| <= C a(m)^{-2}` is written out, with the proof of
  `1 - |phi(t)| >= c T(1/|t|)` from (SPAN) and a symmetrization.
- **Lemma 16.** The finiteness of the zero set, which 05 assumed, is now derived from the same
  count, as the audit asked. The case `n >= 1` is stated, since for `n = 0` the density has no zero.
- **(T1w).** The paper does not use `T_+ ~ T_-` at the scale N, which comparability of the scales
  at `a(N)` does not give. It keeps `T(N) T'(N)` and compares indices, with equal indices.
- **Part (iv) range.** The proof of `thm:zone-diff` gives `L >= K B_N`, which is wider than the
  stated `j <= (1-p)N - K B_N`. The paper states the narrower range, which is implied.
- **The matching at `N^{1-eta}`.** The leading term there is `c_a T_+(N)/N`, as in
  `thm:first-diff`.

## The criterion, checked everywhere

The audit refuted "three modes iff `u` nonincreasing" for fair starts. I checked every place in F
that states a monotonicity form.

- `sec_shape.tex`, after `thm:modes-lower`. "for a fresh plus start the profile `(1, u(1), ...)` has
  exactly one local maximum iff `u_-` is nonincreasing on `j >= 1`". This is proved (it is
  `lem:one-max`(b) with `c_0 = 1`), and it concerns only the plus end. Kept.
- `sec_shape.tex`, after `lem:diff-renewal`. "if `u_-` is nonincreasing on `j >= 1`, then
  `u_-(j) > 1/mu_-`". A different statement, proved. Kept.
- The old paragraph after the conjecture ("the condition is not that the profiles be monotone",
  with the zeta fair example) is rewritten after `lem:one-max`. It now adds the law
  `f(1) = 0.6`, `f(2) = 0.3`, `f(n) = c n^{-5/2}` (n >= 3, mass 0.1). There `u(1) < u(2)`, the fair
  law has exactly three modes at N = 1000, 1500, 2000, and the fresh plus law has four. The
  three-mode statement for this law is a finite computation, and the paper says so. The "at least
  four" for the fresh plus start is proved, by `lem:one-max`(b) and `thm:modes-lower`.
- `sec_intro.tex`. the old sentence on the conjecture is replaced. The criterion is stated through
  the profiles, and the text says that it is not monotonicity of the renewal mass function.
- `README.md` of paperF. the conjecture bullet is replaced by the Theorem F bullet, which states
  sufficiency of monotonicity and its necessity only at an end whose profile starts above `u(1)`.
- `verify_modes.py`. its docstring pointed to the conjecture. It now points to the paragraph after
  `lem:one-max`.

## Numerics

New script `verify_mode_count.py`, listed in `verify_all.py`. Output
`data/verify_mode_count_output.txt`, LF, with the sha256 of the script, of `certify_atlas.py` and
the date. It uses the run recursion of `certify_atlas.occupation` and its a priori rounding bound.
The laws are computed in 128-bit mpmath and rounded once. Every sign of a difference, and so every
mode list and every comparison of `u`, is certified against twice the rounding bound.

| Check | Result |
|---|---|
| zeta law, fresh plus and fair, N = 2500, 3000, 3500, 4000 | modes `[1, N/2, N]` and `[1, N/2, N-1]`, smallest relative gap 3.9e-6, bound 1.8e-9 |
| runs >= 2, `u` | `u(2i) > u(2i +- 1)` for `i <= 6`, strictly decreasing on `12 <= j <= 10^4`, smallest relative decrease 4.1e-7, bound 1.1e-8 |
| runs >= 2, fair, N = 2500, 2600, ..., 4000 | exactly 15 modes at `j, N-j` for `j = 0, 2, ..., 12` and at `N/2`, every N. 17, 19, 17 modes at N = 1000, 1500, 2000 |
| law with `f(1) = 0.6`, `f(2) = 0.3`, `u` | `u(1) = 0.6 < u(2) = 0.66`, strictly decreasing on `2 <= j <= 10^4` |
| same law, N = 1000, 1500, 2000 | fair start `[2, N/2, N-2]`, fresh plus `[2, N/2, N-2, N]` |

These agree with 04 R6 and with the audit's independent engine (15 modes from N = 2500, the same
smallest gap 3.9e-5 at N = 2500, three and four modes for the mixed law).

## Literature

- **Kwaśnicki**, "A new class of bell-shaped functions", Trans. Amer. Math. Soc. 373 (2020),
  2255-2280, arXiv:1710.11023. Volume and pages from the AMS listing. The content (Definition 2.1,
  Corollary 1.3) was read in the arXiv version by 05 and the audit. I did not find the MR number,
  so the entry gives the arXiv number instead.
- **Doney**, "A large deviation local limit theorem", Math. Proc. Cambridge Philos. Soc. 105 (1989),
  575-577, MR0985693. I did not read the paper. Berger, Birkner and Yuan (arXiv:2303.12505) cite it
  for local large deviations in the one-big-jump regime under a regularly varying mass function.
  The paper cites it only for that, as a statement about the values `f^{*m}(n)`. Check the exact
  range before submission.

## What remains open (as stated in the paper)

- Unequal scales. the bulk when one `theta_N -> 0`, and the window of `thm:window`.
- A bound on the number of modes valid for every N. Theorem F is eventual, and the threshold
  depends on the laws (N about 2500 for runs of length at least two).
- For the examples. exactly 15 modes for runs >= 2, and exactly three for the mixed law, rest on
  `u` decreasing strictly beyond the computed range. The paper states them conditionally or as
  computations.

## Files

- New. `paperF/sec_modeproofs.tex`, `paperF/verify_mode_count.py`,
  `paperF/data/verify_mode_count_output.txt`.
- Changed. `problem131_levy.tex` (abstract, keywords, bibliography, input of the appendix),
  `sec_intro.tex`, `sec_setting.tex`, `sec_shape.tex`, `sec_verify.tex`, `verify_all.py`,
  `verify_modes.py` (docstring), `paperF/README.md`, `problem131/README.md`, and the outputs in
  `data/` rewritten by the quick run.
- Aux files and `__pycache__` deleted. The PDF is kept. `lean/` was not touched.
