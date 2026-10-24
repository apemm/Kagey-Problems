# Audit of route T7-A: cycle data from controlled modal supports (Theorem 7)

Date: October 24, 2026. Base checkpoint `6add913`. Read-only audit. No manuscript file or note was
edited.

Audited: `research_notes/C theorems 5 and 7/04_T7_cycle_tree.md` (all of it), its script
`04_attraction_check.py` and output `04_attraction_output.txt`, against Target 2 of `00_targets.md`.
Background read: `research_notes/C modal hierarchy and metastability/01_cycle_conjecture_math.md`
(Theorem D with (12) to (15), Section 1E, the prefactor lemma (21) to (24), the critical-window
theorem 2B, the four-state example (27) to (33)). The input the note calls Fact 7.1 was checked
against Proposition `prop:controlled-score` in `kagey-problems/problem131/paperC/sec_reconstruction.tex`
and what its proof uses: `sec_dv.tex` (Proposition `prop:variational`), `sec_firstorder.tex`
(Proposition `prop:rate`, the set `V_F`, Lemma `lem:upper`, Theorem `thm:first`), `sec_secondorder.tex`
(Theorem `thm:local`, Lemma `lem:discrete`), `sec_model.tex` (Lemma `lem:admissible`, hypothesis (H)).
`sec_reconstruction.tex` is untracked at the base checkpoint, so this is the current working-tree
text.

Scripts run. (a) The note's check script, copied with `05_core.py` into a local scratch folder `t7`
and run there with `py -I` (so the archived output was not overwritten). It ran in 91 s and its
output is byte-identical to `04_attraction_output.txt` (138 proper faces, 0 violations). (b) Two
scripts of mine in the same scratch folder: `mine.py` (prefactors, depths, envelope and endpoints
of (27), the masking rate for `F = {1}`, the singleton-field shift) and `mask2.py` (a 3-state family
where suppression reads off `D(F)` exactly). Both use `mpmath` at 300 to 400 digits at
`t = 10^{-10}, 10^{-20}, 10^{-30}, 10^{-40}`. Copy them next to this file if they are to be kept.

## 0. Verdict in one paragraph

The mathematics of the three theorems is sound. Theorem 7.7 (the attraction design), Lemma 7.5 (Theorem
D for the chain with a cemetery), Lemma 7.9 (strict growth along nested cycles, no reversibility),
Theorem 7.10 (cycles from depths) and Theorem 7.11 (i) and (ii) (prefactors of envelope faces) are
proved as written. I checked every case of the competition in Theorem 7.7 (b), and the four kinds of
faces are exhaustive. The note's one named hypothesis, Fact 7.1, is **already discharged**:
Proposition `prop:controlled-score` as now written in `sec_reconstruction.tex` is stated with
`lambda_F(v) = -rho(Q_F + diag v_F)` for a general irreducible `Q`, its proof uses only lemmas
proved without reversibility, and it applies at each fixed `eta` to an `eta`-dependent field. So the
note's status line ("first unresolved implication is the rewriting of C-P3") is out of date. The
defects are in the side statements. The most serious is in Section 2. The universal claim "no choice
of `M` makes the leaving height equal `D(F)`" is false. I give a 3-state family with fixed `M` where
the winner leaves `F` exactly at `D(F)`. The correct statement is weaker: the leaving height is
at least `D(F)`, sometimes equal and sometimes larger, so it does not determine `D(F)`. Proposition 7.3
is false as literally worded, because a winner's interval can be cut by the critical height of a
face that never wins. It needs a one-line rewording. Theorem 7.11 (iii) overstates at the endpoint
`a_124 = 2/3`. I recomputed the four-state example. The endpoints are `3/4` and `3/2`, and
`a_12 = 2`, `a_123 = 2/3`, `a_124 = 2`. The recursion (7.7) returns the first two, and `{1,2,4}` gets only
`2/3 <= a_124 <= 2`.

## 1. Gaps ranked by severity

No gap invalidates a theorem meant for the paper. Ranked from most to least serious:

1. **Section 2, the negative claim on suppression is overstated (moderate).** The note writes "No
   choice of `M` makes the leaving height equal `D(F)`" and "a growing `M` only raises the masked
   leaving height". Neither is proved. The first is false. Counterexample (script `mask2.py`):
   three states, `V_12 = 2`, `V_13 = 5`, `V_21 = V_23 = 0`, `V_31 = V_32 = 6`, `F = {1}`, `M = 1` fixed.
   Here `D({1}) = 2`. The exact winners at `t = 10^{-20}` and `10^{-40}` are `{1}` at `h = 1.5, 1.9` and the
   mixed face `{1,2}` at `h = 2.1, 2.5, 3, 4, 5.5`. The winner leaves `F` at `D(F)` exactly. The
   mechanism: an excursion to state 2 returns to 1 with probability of order one (cost-0 return), so
   `lambda_E(v) <= (1 - kappa) r_F`, which is the case the note itself sets aside ("only when ...").
   The masking does happen in other families, and there it is real and provable. For `F = {1}` in
   (27) with fixed `M` I get `r_{1} - lambda_E(v) = (t^3/M)(1 + o(1))` (`mine.py`, values `1.000` and
   `0.100` times `t^3` for `M = 1, 10` at two values of `t`). So `{1}` keeps a bounded score up to
   `h = 3 > D({1}) = 2`. **Fix:** replace the decision paragraph by "the leaving height is at least
   `D(F)` (Proposition 7.4 (iii)). It equals `D(F)` in some families and is strictly larger in others,
   for example `F = {1}` in (27), where it is `3`. So it does not determine `D(F)`". Drop the claim
   about growing `M`, or prove it. Proposition 7.4 itself is unaffected.

2. **Proposition 7.3 as worded is false (moderate, wording only).** It says the right end of "a
   maximal open interval of noncritical heights" on which `W` wins is `D(W)`. In (27) the depth `1` of
   state 2 is critical, so `(0,1)` is such an interval for `W = {4}`, with right end `1`, not
   `D({4}) = 2`. The note's own example shows this ("The depth 1 of state 2 lies inside the interval
   of `{4}`"). The proof shows something stronger. The eligible set shrinks as `h` grows, so once
   the winner changes the old winner is never eligible again. Hence the set of noncritical heights
   at which `W` wins is an interval minus finitely many critical points, and its supremum is
   `D(W)`. **Fix:** state it that way.

3. **Uniqueness of the minimizer is used silently (minor).** Proposition 7.3, Proposition 7.4 (i)
   and (ii), and the envelope of Theorem 7.11 speak of "the winner". Equal-cardinality eligible faces
   are compared by `r_G(eta)`. If two of them have identical rates, as `{1,2}` and `{3,4}` in the tied
   family F1 for `1 < h < 4`, Fact 7.1 does not apply and the observable is undefined there. Add "on
   the parameter set where the minimizer is unique", which is the observation model of
   `sec_reconstruction.tex` anyway. Theorem 7.7 does not need this. The target's score tends to
   `-infinity` and every other score stays above it, so the attraction design works on tied
   families. That is a real strength of the design and worth saying.

4. **Theorem 7.11 (iii), the endpoint of the range (minor).** "Every value in that range gives the
   same winners" fails at the lower end. With `a_124 = 2/3` the line `2 + (2/3)x` coincides with that of
   `{1,2,3}` on the whole middle interval, so (26) has no unique minimizer there. From the observation
   alone one gets `a_124 >= 2/3`. One gets `a_124 > 2/3` only if one assumes that the observed winners
   are the strict envelope minimizers of (26). State the range as `[2/3, 2]` with that caveat, or as
   `(2/3, 2]` under the strict-envelope assumption.

5. **Observation model (minor).** (a) Theorem 7.11 uses `eta`-dependent heights
   `h = gamma + eta log x`, that is `tau = x e^{gamma/eta}`. That is outside the fixed-`h` map
   `(h, v) -> winner` of Target 2. It is the model of Section 2B of the cycle note and is allowed by
   (7c), but the note should state it. (b) The definition of `tau(G)` refers to "noncritical" heights.
   The observer does not know the critical set before the depths are reconstructed. Nothing is lost.
   Part (a) of Theorem 7.7 excludes every `h > gamma`, and part (b) gives a win on an open interval,
   so "at some height `h > gamma` at which the winner is defined" works.

6. **Constants in Lemma 7.4a and Proposition 7.4 (minor).** (7.2) is correct. In the proof of 7.4
   (iii), `c = p/(d+1)` assumes `2 r_{G_in}/(p M_0) <= 1`, which fails if `D(G_in) = 0` and `M_0` is
   small. Use `c = p/(d + 2(d-1)/(p M_0))`, valid since every rate is at most `d - 1`. No conclusion
   changes.

7. **Lemma 7.5, scope of Theorem D (minor, justified).** Theorem D in the cycle note is stated for the
   unit-prefactor family (2). The enlarged chain has rates `c t^gamma` and `t^L`. The proof of Theorem
   D goes through (14) and Catoni's Proposition 4.11, and that proposition is for rare-transition
   families in Catoni's Definition 2.1, which allow bounded prefactors. The uniformization constant
   must exceed the largest total rate, which is `max(d - 1, c) + d t^L`, not `d`. When `gamma < 0` the
   rescaling means multiplying all rates by `t^{-gamma}` (cost shift `-gamma`), as in Section 1A. I
   checked the comparison of cycles: before killing, the enlarged chain is coupled to the `Q`-chain.
   So `{Q`-chain leaves `C` before `y}` is contained in `{`enlarged chain is killed or leaves `C`
   before `y}`, and every enlarged cycle inside `E` is a `Q`-cycle. The note should add these two
   sentences. The lemma is proved.

8. **Section 6 and the status line are out of date (editorial).** They name the non-reversible form
   of C-P3 as the open input. Section 7 below shows the paper's Proposition already has that form.

9. **Remark 7.8, last sentence (editorial).** "A reference built on a singleton therefore has depth
   at most `Gamma(i)`" is unclear. The rest of the remark is correct. The determinant
   `c t^gamma q_j - q_ij q_ji` is right, and in (27) the script gives `lambda = -1.0 t^2` for `{1,2}`,
   `{1,2,3}` and `E` at two values of `t`.

## 2. Proposition 7.3 (unperturbed path)

The first sentence is Section 1E of the cycle note. The monotonicity argument is right. Write
`S(h) = {G : D(G) > h}`, which decreases in `h`. If `W` minimizes `(|G|, r_G)` over `S(h_1)` and `W` is in
`S(h_2)` with `h_2 > h_1`, then `W` minimizes over `S(h_2)`. Above `D(W)` its score diverges while `E` keeps
the score `d - 1`. The window at `D(W)` has zero width in `h`. The example is correct. I checked the
singletons: `q_4 = t^2 + 2t^4 < q_1 = t^2 + t^3 + t^5 < q_3 = 3t^2`, so `{4}` wins on `(0,2)`. The only pair of
depth greater than 2 is `{1,2}`, so it wins on `(2,3)`. Above 3 the winner is `E`. With the rewording of
gap 2 and the uniqueness proviso of gap 3, the proposition is **correct after a stated restriction**.

## 3. Lemma 7.4a and Proposition 7.4 (suppression)

**Lemma 7.4a.** With the field `-M` on `G_out`, `A_G - diag v = A_G + M 1_{G_out}`. The Green matrix has
row sums `E_x zeta` and Perron root `1/lambda_G(v)`, so `lambda_G(v) >= 1/max_x E_x zeta`. I checked the
three estimates. From a state of `G_out` the killing clock `M >= M_0` competes with jumps of total rate
at most `d - 1`, so each step there kills with probability at least `p`. The return probability of a
`G_out` sojourn is at most `1 - p`, and its mean length is at most `1/(p M_0)`. A `G_in` sojourn is a sojourn of
the original chain, of mean at most `M^exit_{G_in} <= |G_in|/r_{G_in}` by (14). The number of `G_in`
sojourns is dominated by a geometric variable of mean `1/p`. The number of `G_out` sojourns is at most
that plus one, and `1/p + 1 <= 2/p`. The "Wald" step is really an optional-stopping bound: each
sojourn length has conditional mean bounded given the past, and `{k <= number of sojourns}` is
measurable before sojourn `k`. That is enough. The bound (7.2) follows. The upper bound and
`lambda_E(v) <= r_F` are monotonicity. **Proved as written** (constant remark in gap 6).

**Proposition 7.4.** (i) For noncritical `h` in `(0, D(F))`: suppressed faces have score at least `tau M_0`.
Mixed faces with `D(G_in) < h` diverge by (7.2). Mixed faces with `D(G_in) > h` have a positive rate, so
their score is at least `m_G >= m_{G_in} + 1`, while `G_in` scores `m_{G_in} + o(1)`. `E` is a mixed face
with `G_in = F` and is covered. The inner competition is Section 1E restricted to subfaces of `F`. The
step "minimal cardinality forces the minimizer to be a cycle" uses Theorem D inside the inner face,
which is legitimate because a cycle inside an inner face is inner. (ii) is the argument of 7.3.
(iii): above `D(F)` inner faces have `tau r_G >= tau r_F`, and mixed faces and `E` have
`tau lambda >= c tau r_F`, so all scores diverge. An inner face with `D(G) < D(F)` has
`r_G - lambda_E(v) >= r_G - r_F >= r_G/2`, so it loses to `E`. (iv) holds at all `h > 0` because
`lambda_G(v) >= M_0` against `lambda_E(v) <= r_F`. **Proved as written**, with the uniqueness proviso for
"the winner" in (i) and (ii). The masking discussion after it is a different matter: see gap 1. The
statement "the leaving height is at least `D(F)`" is proved. "Strictly larger" holds in some families
and fails in others.

## 4. Lemma 7.5 and Theorem 7.7 (attraction design)

**Identity (7.4).** `A_G - diag(c t^gamma 1_G) = A_G - c t^gamma I`, so `lambda_G = r_G - c t^gamma` exactly. Correct.

**Lemma 7.5.** The killed matrix of the enlarged chain on `G` is `A_G + s 1_{G cap K}`, for any `L`. Theorem D
for the enlarged chain gives existence and the maximum over enlarged cycles inside `G`. The coupling
gives that every enlarged cycle inside `E` is a `Q`-cycle. Monotonicity gives the reverse
inequality. `D^K(C) = D(C)` when `C` misses `K` is immediate. `lambda_min(A_C + sI) = r_C + s >= s` gives
`D^K(C) <= gamma` when `C` is inside `K`. Proved (see gap 7 for two sentences to add).

**Theorem 7.7 (a).** If `gamma > D(G)`, then `lambda_G(v) = r_G - c t^gamma >= t^{D(G) + eps}/2 > 0`, so the
score diverges for `h > gamma`. If `gamma = D(G)` and `c < a_G`, then `lambda_G(v) = (a_G - c + o(1)) t^gamma` by (21),
and the score diverges for `h > gamma`. Against this, `v >= 0` gives `lambda_E(v) <= 0`, so `E` scores at most
`d - 1`. Correct. The prefactor lemma (21) is proved for non-reversible families in the cycle note.

**Theorem 7.7 (b), the competition at every `h` in `(max(gamma, D^-(C)), D(C))`.** The score of `C` is
`m_C + tau r_C - c e^{(h - gamma)/eta}`, which tends to `-infinity`. Every face `G != C` is exactly one of the
following four kinds, and I checked each:

- *Disjoint from `C`:* `v = 0` on `G`, rate `r_G > 0` (`G` is proper, since `E` contains `C`), score at
  least `0`.
- *Proper subface of `C`:* the same shift on both, so the difference is `tau(r_G - r_C)`, with
  `D(G) <= D^-(C) < h`. It diverges.
- *Strict superset (including `E`):* `lambda_C - lambda_G = r_C - lambda_min(A_G + s 1_{G minus C})`.
  The last term is at least `0`, also for `G = E` because `A_E` is a singular M-matrix and adding a
  nonnegative diagonal keeps the least eigenvalue at least `0`. So the score gap is at least
  `1 - tau r_C -> 1`.
- *Mixed:* `lambda_G - lambda_C = lambda_min(A_G + s 1_K) - r_C` with `K = G minus C`. Every `Q`-cycle in `G` lies
  in `G cap C` or in `K`, by laminarity. A cycle meeting both would be nested with `C`. It is not
  inside `C`, since it meets `K`, and it does not contain `C`, since `C` is not inside `G`. So
  `D^K(G) <= max(D^-(C), gamma) < h`, and `tau lambda_min(A_G + s 1_K) -> infinity` while `tau r_C -> 0`.

So the competition against `E` and against every other face is fully controlled on that interval.
The theorem claims nothing above `D(C)`, and the definition of `tau(G)` needs nothing there. Remark 1
is honest about this. The interval is nonempty by Lemma 7.9. For singletons the mixed kind is empty,
and the interval `(gamma, D(C))` may lie in `h < 0`. That is allowed, since `tau = e^{h/eta}` is a fixed
positive number at each `eta`. **Proved as written**, given Fact 7.1 (Section 7).

**Theorem 7.7 (c).** This follows from (a), (b), monotonicity and Theorem D. Proved.

**Script.** The re-run reproduces the archived output exactly. Its limits should be stated. It works
on a `gamma` grid of step `1/2`, so it confirms `tau(G) = D(G)` only to within that resolution, and it uses the
leading score (7.1) at two values of `t`, not the iterated limit. Since the proof covers all of this,
the check is evidence, as the note says.

## 5. Lemma 7.9 and Theorem 7.10 (cycles from depths)

**Lemma 7.9.** I checked the round construction. Start at `y` in `C'`, a maximizer of
`E_y tau_{C'^c}`. A round ends outside `C` in one of two ways. Either the chain leaves `C'` directly
into `C^c`, before visiting `z` in `C minus C'`, which is the event `{tau_{C^c} < tau_z}` from `y`. Or,
from the entry state `w` in `C minus C'` (so `w != y`), it leaves `C` before `y`. Each has probability at
most `e^{-alpha/eta}` by (7), with `alpha` the minimum over finitely many pairs. Rounds that do not end
outside `C` end at `y`, so rounds are i.i.d. by the strong Markov property. `R` is geometric with
`E R >= e^{alpha/eta}/2`. `{R >= k}` depends only on rounds `1` to `k - 1`, and the first parts of the rounds
have mean `M^exit_{C'}` and sum to at most `tau_{C^c}`. So Wald's identity applies. Then
`D(C) >= D(C') + alpha` by (14) and the existence of the limits in Theorem D. Neither reversibility nor
uniqueness of bottoms is used. **Proved as written.**

**Theorem 7.10.** (i) implies (ii) is Lemma 7.9 with Theorem D. (ii) and (iii) are equivalent by
monotonicity of `D` (every proper subset lies in some `C minus {i}`). (ii) implies (i) because the
cycle `C*` inside `C` with `D(C*) = D(C)` given by Theorem D cannot be proper. `Gamma(C) = D(C)` is part of
Theorem D, and laminarity is quoted (Catoni, and Cirillo, Nardi and Sohier 2015, Proposition 2.4,
which is for general rare-transition dynamics). **Proved as written.** No nondegeneracy is needed.

**Tied example.** Here `U = (0,0,0)` and `H_ij = 1`, so every `q_ij = t`. Then `r_{i} = 2t`, and `A_{12}` has
eigenvalues `t, 3t`, so `D({1}) = D({1,2}) = 1`. From 1 the chain exits `{1,2}` before hitting 2 with
probability `1/2`, so `{1,2}` is not a strict cycle. Criterion (ii) rejects it, and the weak criterion
accepts every proper set. It is the smallest such example, because with two states every proper face is a singleton.
Correct.

## 6. Theorem 7.11 (prefactors from window endpoints)

**Recomputation of (27) at `gamma = 3`.** `mine.py` gives depths `2, 1, 2, 2` for the singletons, `3` for
`{1,2}`, `{1,2,3}`, `{1,2,4}`, and `2` for every other proper face. At `t = 10^{-20}` and `10^{-40}` it gives
`r/t^3 = 2.0, 0.666666666667, 2.0` for `{1,2}`, `{1,2,3}`, `{1,2,4}`, in agreement with (32). The lines are
`1 + 2x`, `2 + (2/3)x`, `2 + 2x`, `3`. The crossings are `1 + 2x = 2 + (2/3)x` at `x = 3/4` and
`2 + (2/3)x = 3` at `x = 3/2`. A scan over `x` in steps of `1/100` gives winners `{1,2}`, `{1,2,3}`, `E` and never
`{1,2,4}`, whose line is `1` above that of `{1,2}`.

**Backward recursion by hand.** `alpha_E = 0`. Then `a_123 = 0 + (3 - 2)/(3/2) = 2/3` and
`a_12 = 2/3 + (2 - 1)/(3/4) = 2/3 + 4/3 = 2`. Both match. For `{1,2,4}`, the supremum of
`(env(x) - 2)/x` is `2/3`, attained on the whole middle interval, so `a_124 >= 2/3`. Monotonicity against
`{1,2}`, the only subface of depth `3`, gives `a_124 <= 2`. No superset of depth `3` exists, so there is
no further bound. So `a_12` and `a_123` are recoverable, and the true `a_124 = 2` is not.

**Proof.** (i): lines of positive slope eventually exceed the flat line of `E`, and a concave envelope
has slope `0` only on its last piece. (ii) is the crossing identity. (iii) is right up to the endpoint
(gap 4). On "absolute reference": the anchor is the slope `0` of the last piece, which holds for any
face of depth greater than `gamma`. `E` guarantees that such a face exists. The wording "because
`lambda_E(0) = 0`" is fine but slightly narrower than needed.

**Calibrated singleton field.** I checked the claim numerically. With `v = c t^3 e_1`, `c = 1, 5`, at
`t = 10^{-30}`, `(lambda_G(v) - lambda_G(0))/t^3` equals `-c` to ten digits for `{1,2}`, `{1,2,3}`, `{1,2,4}` and `E`.
For `E` this needs the spectral gap of `Q` to be much larger than `t^3`. It is, of order `t^2`, since state 1 is
the only metastable state at scale `t^3`, so first-order perturbation applies. So all window lines
shift by `-cx` and the endpoints do not move. The note's conclusion holds. The open question it
leaves (another calibrated field separating `a_124` from `a_12`) is honestly labelled. The attraction
field on `{1,2,4}` itself does not help, because it shifts `{1,2}` by the same `-c t^3` at leading order.

**Verdict.** (i) and (ii) are proved as written. (iii) is correct after the endpoint restriction.

## 7. Fact 7.1 against Proposition `prop:controlled-score`

The question is whether the Proposition as stated covers what Fact 7.1 needs.

- **Non-reversible `Q`: covered.** The Proposition defines `lambda_F(v) = -rho(Q_F + diag v_F)`, the
  Perron root of a general irreducible Metzler matrix, which is the note's "smallest real
  eigenvalue of `A_G - diag v_G`". Its proof uses Lemma `lem:upper` with `theta = q - v - lambda_F(v) 1`,
  which is in `V_F` because the right Perron vector is positive. It also uses Proposition
  `prop:variational`, whose minimizer is `l o r` with left and right Perron vectors and is proved
  through Proposition `prop:rate`, which states "without reversibility". The other inputs are
  Theorem `thm:first` (i), through Theorem `thm:local` and Lemma `lem:discrete` (both under (H)
  only), and Lemma `lem:admissible`. None of these assumes symmetry. The only symmetric object in the
  local-law proof is a Hessian (`app_torus.tex`), which is symmetric for any `Q`. The symmetrized
  `S_F` appears only in the reversible special case of Proposition `prop:variational`. The note's
  statement that the controlled score law is written with `lambda_min(S_F - diag v)` refers to the
  outline, not to the current draft.
- **Fields that depend on `eta`, at fixed `eta`: covered.** The Proposition fixes `Q`, `mu`, `v` and a
  compact `tau` interval, with constants depending on them. At fixed `eta`, `v(eta)`, `Q_eta`, `mu_eta` and
  `tau = e^{h/eta}` (or `x e^{gamma/eta}`) are fixed. The field may have either sign and `lambda_F(v)` may be
  negative. The proof does not use the sign: `theta_i = sum_j q_ij r_j/r_i > 0` regardless.
- **Order of limits (`N` first, then `eta`): covered.** The Proposition is a statement as `N -> infinity` at
  fixed data. Fact 7.1 applies it once for each `eta` and makes no uniformity claim in `eta`, which
  Remark 3 of the note also says.
- **Full support, admissibility, `F = E`.** All rates are positive, so every face is irreducible.
  With `mu` of full support every face is admissible by Lemma `lem:admissible` (b). The Proposition
  covers `F = V`. Its error term `O(log L)`, with `L = log N`, is the note's `O(log log N)`. Its last
  sentence ("if `F` is the unique minimizer ... every maximizer has support `F` for all large `N`") is
  exactly the first statement of Fact 7.1, and the second follows from finiteness.

**Nothing is missing.** The one thing to change is the note's wording in Section 6 and the status line.

## 8. Verdict per statement

| Statement | Verdict |
|---|---|
| Fact 7.1 | Proved: it is Proposition `prop:controlled-score` applied at each fixed `eta`. Covers non-reversible `Q`, `eta`-dependent fields and the order `N` then `eta`. |
| Fact 7.2 | Proved as written. |
| Proposition 7.3 | Correct only after a stated restriction: the winning set of `W` is an interval minus finitely many critical heights, with supremum `D(W)` (as worded it is false, e.g. `{4}` on `(0,1)` in (27)), and the minimizer must be unique. |
| Lemma 7.4a | Proved as written (the constant `c = p/(d+1)` used later needs the adjustment of gap 6). |
| Proposition 7.4 (i) to (iv) | Proved as written, with the uniqueness proviso for "the winner". |
| Section 2 masking claims | Incomplete and partly false. "Leaving height `>= D(F)`" is proved. "Strictly larger" holds for `F = {1}` in (27) (leaving height `3`). "No choice of `M` gives `D(F)`" is false (3-state counterexample, gap 1). "Growing `M` raises it" is unproved. |
| Lemma 7.5 | Proved (add the coupling sentence and the uniformization constant). |
| Lemma 7.6 | Quoted from Catoni and from Cirillo, Nardi and Sohier. Correct citation for general dynamics. |
| Theorem 7.7 (a), (b), (c) | Proved as written. The competition at every `h` in `(max(gamma, D^-(C)), D(C))` is complete over the four kinds of faces, including `E`. Replace "noncritical" in the definition of `tau(G)` by "at which the winner is defined" (gap 5). |
| Remark 7.8 | Correct (last sentence unclear). |
| Lemma 7.9 | Proved as written, for non-reversible families. |
| Theorem 7.10 | Proved as written, with no nondegeneracy. Tied three-state example correct and minimal. |
| Theorem 7.11 (i), (ii) | Proved as written. Four-state values `a_123 = 2/3`, `a_12 = 2` confirmed. |
| Theorem 7.11 (iii) | Correct only after a stated restriction: the range is `[2/3, 2]` from observations, with the lower endpoint excluded only under a strict-envelope assumption. |
| (7d) no reversibility | Correct. Every step, including Fact 7.1 through the current Proposition, holds for non-reversible families. |

The note's overall status can be raised from "proved under a stated hypothesis" to "proved" for (7a)
by attraction, (7b) and (7c). Two edits remain: the negative claim about suppression should be cut
to what is shown, and Proposition 7.3 should be reworded.
