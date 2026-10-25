# 21. Audit of the mode-count integration into Paper F (25 October 2026)

Audited: `paperF/sec_shape.tex` Section 6.5 (`sec:mode-count`), `paperF/sec_modeproofs.tex`
(Appendix B), the abstract in `problem131_levy.tex`, `sec_intro.tex`, `sec_verify.tex` (the new
paragraph) and `paperF/README.md`, against `Paper F modes O1/04_report.md`, `05_report.md`,
`06_audit.md` and the integration record `20_mode_count_integration.md`. Read-only. The numerics use
a new engine written for this audit, outside the repository (scratch folder `a21/`: `eng21.py`,
`val.py`, `big.py`, `big2.py`, `chk_b.py`). No script of the paper or of 04/05/06 was run.

## Verdicts

| Item | Verdict |
|---|---|
| 1. `lem:one-max` | proved as written. Three wording slips in the paragraph after it (below) |
| 2. `f(1) = 0` gives at least five modes for the fair start | proved as written |
| 3. At least 15 modes for runs >= 2 | correct after a stated restriction: for the law `f(n) ∝ n^{-5/2}`, `n >= 2`, and the fair start. The example says so. The abstract, the introduction and the README do not, and as worded there the claim is refuted |
| 4. Theorem F, `lem:diff-bigjump`, corollaries vs the audited versions | proved as written. Every fix of 06 is in. Theorem 1′ is not claimed |
| 5. Abstract and introduction | correct after a stated restriction: the fifteen-mode sentence must be restricted. The rest stays within the theorems |

## 1. `lem:one-max`

**Own derivation of the critical step (necessity in (b)).** Let `c_0 > u(1)` and `u(i+1) > u(i)` for some
`i >= 1`. By `lem:diff-renewal`, `u` is eventually strictly decreasing with limit `1/mu > 0`, so
`u(j) > 1/mu` for all large `j` and `sup_{j > i} u(j) > 1/mu`. A supremum above the limit is attained.
The maximal block of equal values through a maximizer `j*` cannot contain `i`, since
`u(i) < u(i+1) <= u(j*)`. So it lies in `[i+1, oo)`, both neighbours are strictly smaller (they are `<=` the
maximum and differ from it by maximality of the block), and it is a local maximum. `{0}` is another, since
`y_1 = u(1) < c_0`. Two distinct local maxima.

**Implications checked.**
- (a) Blocks starting at `a >= 2` have `y_{a-1} > y_a`. If `c_0 > u(1)`, `{0}` is the only one. If
  `c_0 <= u(1)`, the block through `1` (which contains `0` when `c_0 = u(1)`) is finite, by eventual strict
  decrease, and ends with a strict decrease. Correct in all three cases.
- (c) With `c_0 < u(1)`, `0` is a singleton block that is not a local maximum, and the blocks on `j >= 1`
  are those of `(u(j))_{j>=1}`, with the same left condition at `1`. Correct.
- The text reads (b) as covering every end with `c_0 > u(1)`. This includes the fresh start at its own end
  and also the fair start when `f(1) < 1/2`. The paper and the README ("necessary only at an end whose
  profile starts above `u(1)`") state exactly this, which is right. A summary that says "necessary only
  for the fresh-start profile at its own end" is too narrow.

**Slips in the paragraph after the lemma.**
1. "The profile at the other end has `c_0 = 0`, and (c) applies." This needs `f(1) > 0`. When `f(1) = 0`
   the profile starts with the tie `0 = u(1)`, and neither (b) nor (c) applies (nor the no-tie condition).
2. "In case (c) monotonicity of `u` is sufficient by (a) but not necessary." The only witness is the law
   `f(1) = 0.6`, `f(2) = 0.3`, whose `u` is shown decreasing on `2 <= j <= 10^4` by computation and not
   beyond. The zeta example shows a nonmonotone profile, not a nonmonotone `u`. So "not necessary" rests
   on a computation over a finite range and should say so (or read "not necessary in the computed
   example").
3. "For the fresh plus start the profile `(1, 0.6, 0.66, ...)` has two local maxima by (b)". (b) gives
   *at least* two. The conclusion "at least four modes" that follows is correct.

Spot-check (own engine): `u = 0.6, 0.66, 0.614947, 0.609309, ...`, strictly decreasing on `2..10^4`. Fair
start modes `[2, N/2, N-2]`, fresh plus `[2, N/2, N-2, N]` at `N = 1000, 1500, 2000`. Agrees with the paper.

## 2. At least five modes when `f_+(1) = f_-(1) = 0`

**Derivation.** Fair start: `kappa_±(0) = 1/2` and `u_∓(1) = f_∓(1) = 0`, so `c_0 = 1/2 > u(1)`. `u` is not
nonincreasing on `j >= 1`, since `u(1) = 0` and `u(j) -> 1/mu > 0`. By `lem:one-max`(b) each profile has
at least two local maxima, so `M_± >= 2`, and `thm:modes-lower` gives at least `2 + 2 + 1 = 5` modes for
all large `N`. Hypotheses of `thm:modes-lower`: (RV), (SPAN) for both signs, `nu_± = f_±/2 = o(T_±)`,
and `kappa_±(0)` exist. All hold. (SPAN) is a real restriction here (a law on even lengths only is
excluded), and it is the standing assumption of the lemma. No (EQ), (LR) or no-tie condition is needed.

**Spot-check** with my own recursion (float64, validated against a sum over all sign strings at
`N = 5, 9, 13` for three pairs of laws and all three starts, error `<= 1.3e-15`). Plus runs
`f(n) ∝ n^{-2.4}` on `n >= 2`, minus runs `f(n) ∝ n^{-2.5}` on `n >= 3` (unequal laws, unequal indices),
fair start. Modes: 12, 14, 18, 15, 14, 14 at `N = 500, 1000, 1500, 2000, 2500, 3000`, smallest relative gap
`1.3e-6`. Consistent with at least five.

## 3. At least 15 modes for runs >= 2

**What the example proves.** For `f(n) = n^{-5/2}/(zeta(5/2) - 1)`, `n >= 2`, both signs, fair start:
- `u(2i) > max(u(2i-1), u(2i+1))` for `1 <= i <= 6` is a finite computation of 13 values. I recomputed
  them at 50 digits: the signs of `Δu` on `j = 1..20` are `+-+-+-+-+-+---------`, smallest `|Δu|` on
  `1..12` is `2.0e-4`. With `{0}` (since `1/2 > u(1) = 0`) this gives seven local maxima per profile, at
  `j = 0, 2, ..., 12`, and at least 15 modes for all large `N` by `thm:modes-lower`. Proved, modulo a
  certified finite computation, which the paper discloses.
- Exactly 15 is stated conditionally ("If it decreases strictly on `[12, oo)`"), with `u` checked only on
  `12 <= j <= 10^4`. The no-tie condition with `J = 12` and exactly seven maxima follow from the computed
  alternating signs. Honest as written.
- The computed counts agree with my engine: 17, 19, 17 at `N = 1000, 1500, 2000`, and 15 at every
  `N = 2500, 2600, ..., 4000`, modes at `j, N - j` for `j = 0, 2, ..., 12` and at `N/2`. Smallest relative
  gap `6.3e-6`. `u` strictly decreasing on `12..10^4`, smallest relative decrease `4.1e-7`.

**What is not proved, and is claimed elsewhere.**
1. *Other power tails.* The abstract says "Runs of length at least two give at least fifteen modes", the
   introduction "runs of length at least 2 with a power tail give at least 15", and the README the same.
   Counterexample: `f(n) = n^{-12/5}/(zeta(12/5) - 1)`, `n >= 2`, both signs (index 7/5; it satisfies
   (SPAN), (LR), (LD2), (EQ)). Here `u` has peaks at `j = 2, 4, 6, 8, 10` only (signs of `Δu` on `1..14`:
   `+-+-+-+-+-----`), strictly decreasing on `10..10^4`. Each profile has six local maxima, so the proved
   lower bound is 13, and Theorem F gives exactly 13 if `u` decreases on `[10, oo)` (the same status as the
   paper's own exactly-15 claim). My engine gives 17, 15, 13, 13 modes at `N = 1000, 2000, 3000, 4000`.
   So the number 15 belongs to the index-3/2 law, not to runs >= 2 with a power tail. The general proved
   statement is at least five.
2. *Other starts.* The abstract does not say "fair start". For a fresh plus start with the paper's own law,
   the minus-end profile is `(0, 0, u(2), ...)`, which has a tie at `j = 0` and six local maxima, so the
   lower bound is `7 + 6 + 1 = 14`, and Theorem F does not apply (no-tie fails). My engine gives 14 modes at
   `N = 2500` and `3000`.
3. `rem:mode-open`: "settles at 15 from `N = 2500`". The computation covers `N = 2500, 2600, ..., 4000`
   only. Suggest "is 15 at every computed `N` from 2500 to 4000".

## 4. Theorem F, the big-jump difference lemma and the corollaries

**Own derivation of the critical step (`lem:second-bigjump`, no giant summand).** With `w = ceil(delta L)` and
`L >= m mu`: `m T(delta L) <= (L/mu) C_delta T(L) <= C_delta L^{1-alpha+eps'}`, a negative power of `L`
with no factor of `a(m)`. The no-giant part is at most `C a(m)^{-2} (m T(w))^{L/(8w)}`, and `L/(8w)` is
about `1/(8 delta)`, so the part is `<= C L^{-(alpha-1-eps')/(16 delta)}`, which is `o(L^{-alpha-3-eps'})`
and so `o(m f(L)/L^2)` once `delta` is small. This is the repair 06 asked for, and the paper uses it.

**Fixes of 06, each checked in the text.**
- Lemma 12c restricted: `lem:second-bigjump` assumes `L >= max(K_1 a(m), L_0, m mu)`. Its two uses satisfy
  it: `lem:tails`(a), range `m <= j/(2 mu)`, has `L >= j/2 >= m mu`; `lem:tails`(b), `m < m_eps`, has
  `x - m mu >= x/2 >= m mu`. No other use (grep). The boundary terms: `m^2 T(L) f(L)/(a(m) L)` against
  `m f(L)/L^2` gives `m T(L) L/a(m) <= C r^{1-alpha+eps'}` by `eq:potter-m`; `m^2 f(L)^2/L` gives
  `m L f(L) <= C m T(L) <= C`. Both correct. The main sum is `C_delta f(L)/L^2` per `i`, so `m f(L)/L^2`
  after summing, which is the target.
- `R = K_0 + 1`: Theorem F(v) is on `|x_{N,k}| <= K_0 + 1`, (iv) on `j <= (1-p)N - K_0 B_N`, i.e.
  `x_{N,N-j} >= K_0`, so they overlap. `K_0 >= R_0` makes `R >= R_0 + 1` as `cor:bulk-sign` needs, and
  enlarging `K_0` only shrinks the range of (iv). Correct.
- Threshold `w`: stated in `lem:plus-second`(i) and in the second boundary term of `lem:second-bigjump`.
- Index slip of Lemma 3: not re-derived here (06 accepted the corrected formula).
- (EQ): in Theorem F, `cor:logconvex-three` and `ex:runs2` (the law is the same for both signs).
  `cor:sequences` replaces it by equal indices and `min theta >= theta_0`, as 06 approved. The junction
  section derives `a_+ ≍ a_-` from (EQ) correctly by Potter's bound.
- Theorem 1′: not in the paper. `rem:mode-open` says only that parts (i) to (iii) hold without (EQ). I
  checked this against the proofs: (i), (ii) are `thm:ends`, and (iii) is `cor:convex`, whose hypotheses
  are (RV), (SPAN), (LR) for the minus sign and (LR), (LD2) for the plus sign. The paragraph after
  `thm:zone-diff` explains why (iv) needs comparable scales and makes no claim.

**Other checks.**
- Proof of the count from the sign pattern. The correspondence local maxima ↔ `(+,-)` pairs, first `-`,
  last `+` (zeros deleted, plateaus once) is right. The transformation "reverse and negate" keeps
  `(+,-)` pairs and swaps first `-` with last `+`; I verified it index by index. The junction pairs
  `σ_+ | (-)^a` and `(+)^d | σ̄_-` are counted once each. Total `M_+ + 1 + M_-`.
- Sign conventions: (iv) `D_N > 0` means `ΔP_N(N-j-1) < 0`, matching (v) to the right of the bulk mode.
- `lem:diff-bigjump` matches 04 Lemma 8 (D0 to D3 and the bound on `q_{m+1}`) with the same quantifiers
  (`C` first, then `K` for each `ε`, all `m >= 1`, no upper bound on `m`). The added case `m = 0` for the
  `q` difference is covered by "use `δV_0 = f`". The Step 1 exponent `(α - ε')/(32 δ) > α + 2 + ε'`
  follows from `L/(16w) >= 1/(32δ)`.
- `thm:zone-diff`: `L >= K B_N` on the stated range (as `s/mu_- >= 1`); the first term of I is
  `o(f(L))` because `(1-η)α > 1`. Correct.
- `cor:three-modes`, `cor:logconvex-three` (no-tie is `f(1) ≠ kappa(0) ∈ {0, 1/2, 1}`, which needs
  `f(1) ≠ 1/2` only for the fair start; `0 < f(1) < 1`), and the zeta remark (`f(1) = 1/zeta(α+1) >
  1/zeta(2) = 0.608`) are correct.

## 5. Abstract and introduction

- Theorem F in the abstract: "For fresh and fair starts, comparable scales and a second-order smoothness
  condition, ... exactly one more than the number of local maxima ..., for all large times." Eventual in
  `N`, (EQ) and (LD2) are present. The no-tie condition is missing; add "and no ties in the profiles" or
  "generic". "This holds for log-convex run laws" should read "strictly log-convex" (and the fair start
  needs `f(1) ≠ 1/2`; the zeta law has `f(1) > 1/2`).
- "Runs of length at least two give at least fifteen modes": refuted as worded (Section 3 above). Suggest
  "Runs of length at least two give at least five modes for the fair start, and fifteen for a pure power
  law of index 3/2."
- Introduction, Theorem F paragraph: hypotheses (LR), (SPAN), (LD2), (EQ), fresh or fair start, no ties,
  "for all large `N`" are all stated. "This holds for all strictly log-convex run laws" omits the fair
  start's `f(1) ≠ 1/2`; minor. "Then the fair start has at least five modes" is right if "runs of length 1
  are impossible" means for both signs. "runs of length at least 2 with a power tail give at least 15":
  refuted as worded; same fix as the abstract. "The comparison (EQ) is needed only at the scale N" omits
  that equal indices are still assumed (`cor:sequences`); add "given equal indices".
- "Every theorem below except Theorems `thm:window` and `thm:mode-count` holds for every relation between
  the two scales": correct.
- Novelty of `lem:diff-bigjump` ("we do not know an earlier statement") is a hedged claim, not checked
  here; Doney (1989) was not read by the integrator, as 20 says.

## Required changes

1. Abstract, introduction and `paperF/README.md` (line 88): restrict the fifteen-mode claim to the fair
   start and to `f(n) ∝ n^{-5/2}` on `n >= 2`; state the general bound as five.
2. Abstract: add the no-tie condition and "strictly" to log-convex.
3. After `lem:one-max`: "(c) applies" needs `f(1) > 0`; "not necessary" rests on the computed example;
   "has two local maxima by (b)" should be "at least two".
4. `rem:mode-open`: "settles at 15 from N = 2500" should name the computed range.
5. Introduction: "(EQ) is needed only at the scale N, given equal indices".

None of these affects a proof. The mathematics of Theorem F, Appendix B and the corollaries holds as
written, with the fixes of 06 in place.

## Fixes applied (25 October 2026)

1. After `lem:one-max` (`sec_shape.tex`). The paragraph now says that (b) makes monotonicity necessary
   at every end whose profile starts above `u(1)`, including the fair start when `f(1) < 1/2`. "(c)
   applies" now needs `f(1) > 0`, and the tie `0 = u(1)` at `f(1) = 0` is named (neither (b) nor (c)
   applies). "Not necessary" is tied to the example with `f(1) = 0.6`, with `u` checked only on a
   finite range. "Has two local maxima by (b)" now reads "at least two".
2. Fifteen modes. The abstract now reads "Without runs of length one the fair start has at least five
   modes, and at least fifteen for a pure power law of index 3/2." The introduction restricts 15 to
   the fair start and `f(n) ∝ n^{-5/2}` on `n >= 2`, and says the index 7/5 law gives 13 at the largest
   computed N. `ex:runs2` ends with the index 7/5 law (lower bound 13, computed 13 at N = 3000, 4000)
   and the fresh plus start (tie at `j = 0`, lower bound 14). `rem:mode-open` names the law, the start
   and the computed range 2500 to 4000. `sec_verify.tex` names the law. `paperF/README.md` (Section
   6.5 summary and the `verify_mode_count.py` entry) is restricted the same way.
3. Abstract. It states the no-tie condition ("no ties in the boundary profiles") and says "strictly
   log-convex". 247 words. `problem131/README.md` also gained the no-tie condition.
4. Introduction. "Given equal indices, the comparison (EQ) is needed only at the scale N."

The 13-mode counts for the index 7/5 law come from the audit engine (`a21/`) and are not reproduced by
a script of the paper. Rebuilt: 80 pages, no errors or undefined references.
`py -I verify_all.py --quick` passes (6 scripts).
