# Route T7-A: Theorem 7, reconstruction of cycle data from controlled modal supports

Base checkpoint: commit `6add913` of this repository. Date: October 24, 2026.

Inputs read in full. `00_targets.md` (this folder). `research_notes/C modal hierarchy and metastability/01_cycle_conjecture_math.md`
(Sections 1 to 3, formulas (1) to (36)) and its script `01_exact_cycle_checks.py`.
`research_notes/Occupation novelty and compact advances/11_C_ready_to_draft_outline.md` (Sections 1 to 6, in particular C-P3 and
the suppression lemma of C-I1). `05_T7_reconstruction_check.md` and `05_core.py` (this folder, route T7-B), read after the
coordinator reported that the suppression design does not read off `D(F)`. Catoni (1999) Definitions 2.1, 4.2, 4.3 and
Proposition 4.11, and Cirillo, Nardi and Sohier (2015) Proposition 2.4 (laminarity of cycles), are used only in the form in
which the cycle note quotes them.

Files written. This note. The script `04_attraction_check.py` (exact-score check of the design of Theorem 7a, imports
`05_core.py`) and its output `04_attraction_output.txt`. Run with `py -I 04_attraction_check.py` in this folder.

Labels. Statements meant for the paper are numbered 7.1 to 7.12. Formula numbers (1) to (36) refer to the cycle note.

## 0. Summary

1. (7a) The suppression design of `00_targets.md` does not read off `D(F)`. We prove what it does give (Proposition 7.4).
   Below `D(F)` the winner is the restricted selection inside `F`, and its transitions sit exactly at the depths of the
   cycles it displays. At and above `D(F)` every score diverges and the leaving height is at least `D(F)`, strictly larger
   in every case computed by T7-B. The cause is that the whole space, once the complement of `F` is killed, has a rate
   of the same order and prefactor as `r_F` (we call this masking). Suppressed singletons never win. Fixed `M` is the right
   choice for Proposition 7.4, and a growing `M` only raises the masked leaving height.
2. (7a) We replace suppression by a calibrated attraction. For a face `G` put `v = c t^gamma` on `G` and `0` elsewhere,
   with `t = e^{-1/eta}`, a fixed known `c > 0` and a known real `gamma`. Let `tau(G)` be the supremum of the `gamma` for which
   `G` is the eventual winner at some height `h > gamma`. Theorem 7.7 proves `tau(G) <= D(G)` for every face, with equality
   for every global cycle, and hence `D(F) = max_{G subset F} tau(G)` for every face `F`. The design needs the time unit
   (the height `h`), the field amplitude `c t^gamma` and the labels. It needs no rate of `Q` and no suppression. The exact-score
   check confirms it on 11 matrices (reversible, non-reversible, tied), with no violation (Section 7).
3. (7a) The boosted-singleton reference `v_i = q_i - c t^gamma` suggested by the coordinator fails. It creates faces with
   negative rate of larger order than `t^gamma`, because every face that contains `i` and a neighbour of `i` gains mass at
   `i` (Remark 7.8, and Part B of the script).
4. (7a) The unperturbed path determines the depth of every winner it shows, as the right end of its interval
   (Proposition 7.3). It misses every cycle that is never the smallest eligible face, and it shows critical noncycle
   winners only on intervals of zero length in `h`.
5. (7b) A face `C` is a global cycle if and only if `D(C) > D(C')` for every nonempty proper subset `C'` (Theorem 7.10). No
   nondegeneracy is needed. The forward direction uses strict growth of depth along nested cycles, which we prove for
   non-reversible families too (Lemma 7.9). Ties do not break the criterion. They break only its weak form, and we give the
   smallest example.
6. (7c) At a critical depth the window endpoints of the unperturbed path determine exactly the prefactors of the faces on
   the lower envelope, and only inequalities for the others (Theorem 7.11). The reference is absolute because the whole
   space has rate exactly `0`. In the four-state example the endpoints `3/4` and `3/2` give `a_123 = 2/3` and `a_12 = 2`, and only
   `2/3 <= a_124 <= 2` for `{1,2,4}`. A calibrated field on a singleton gives no further reference there.
7. (7d) No step uses reversibility. The only input that must still be checked in its non-reversible form is the controlled
   score law C-P3, which the outline states with the symmetrized matrix `S`.

## 1. Setting and three elementary facts

We use the notation of `00_targets.md` and of the cycle note. The costs `V_ij >= 0` are fixed, `q_ij = t^{V_ij}` with
`t = e^{-1/eta}`, and every killed matrix `A_G` keeps the full exit diagonal. A field `v = v(eta)` is a vector in `R^E` that may
depend on `eta` but not on `N`. Write `lambda_G(v)` for the smallest real eigenvalue of `A_G - diag(v_G)` and `m_G = |G| - 1`. At
height `h` we put `tau = e^{h/eta}` and use the score

    Phi_{eta,h}(G, v) = m_G + e^{h/eta} lambda_G(v).                                           (7.1)

**Fact 7.1 (selection at fixed temperature).** Fix `eta`, `h` and `v`. If (7.1) has a unique minimizer `G` over all nonempty
faces, then `G` is the eventual winning support as `N` tends to infinity. If, for all sufficiently small `eta`, a face `G`
satisfies `Phi(G') - Phi(G) >= 1/2` for every `G' != G`, or `Phi(G') - Phi(G) -> +infinity`, then `G` is the eventual winner at all
those `eta`.

*Proof.* At fixed `eta` the field is a fixed finite vector and `tau` is fixed, so the controlled score law C-P3 applies. It
gives `log max = -Phi log N + O(log log N)` on each face. A positive gap in `Phi` dominates the `O(log log N)` terms. There are
finitely many faces. Hence the second statement follows from the first. Note that C-P3 needs a full-support start, which
we assume throughout.

**Fact 7.2 (monotonicity and shifts).** (i) If `G' subset G` then `lambda_G(v) <= lambda_{G'}(v)`, strictly when `G' != G`. (ii) If
`v <= w` entrywise then `lambda_G(w) <= lambda_G(v)`, and `lambda_G(v + kappa 1) = lambda_G(v) - kappa` for every real `kappa`. In
particular `lambda_G(v) >= lambda_G(0) - max_i v_i`. (iii) Adding `kappa 1` to the field does not change the winner at any finite `N`.

*Proof.* `-(A_G - diag v)` is an irreducible Metzler matrix, because all rates are positive. Its Perron root is strictly
monotone under passing to a principal submatrix and monotone in the diagonal. This gives (i) and (ii). For (iii), the
controlled atom is multiplied by `exp(T kappa sum_i n_i / N) = e^{T kappa}`, which does not depend on `n`.

Fact 7.2 (iii) is the source of the masking in Section 2. Only differences of the rates `lambda_G(v)` matter, so a field
that kills the complement of `F` is the same experiment as a field that rewards `F`.

**Proposition 7.3 (the unperturbed path).** Let `v = 0`. Fix a noncritical `h`, that is `h` not a depth of any proper face. For
small `eta` the winner `W(h)` minimizes `(|G|, r_G)` over the faces with `D(G) > h`, the whole space `E` included, and it is a
global cycle (Section 1E of the cycle note). If `W` is the winner on a maximal open interval of noncritical heights, the
right end of that interval is `D(W)`.

*Proof.* The first statement is 1E of the cycle note. As `h` grows the set of eligible faces `{G : D(G) > h}` only shrinks. So
the smallest eligible cardinality does not decrease, and between two equal cardinalities the comparison is by `r_G`, which
does not depend on `h`. Hence `W` keeps winning as long as it is eligible, that is up to `D(W)`. Above `D(W)` its score
`m_W + e^{h/eta} r_W` diverges, while `E` has the finite score `d - 1`, so `W` loses. At the critical height `D(W)` the window of
Section 2B of the cycle note opens, but its macroscopic width in `h` is zero.

Hence the unperturbed path determines the depth of every winner it shows. It misses the rest. In the four-state example (27)
the path is `{4}` on `(0,2)`, `{1,2}` on `(2,3)` and `E` above `3`, with the noncycle `{1,2,3}` inside the window at `3` only. It
shows `D({4}) = 2` and `D({1,2}) = 3` and nothing about `{1}`, `{2}`, `{3}` (depths `2, 1, 2`). The depth `1` of state `2` lies inside the
interval of `{4}`. Note that the reason this path is free of masking is that `lambda_E(0) = 0` exactly. This is the property the
design of Section 3 keeps.

## 2. Suppression: what it gives and why it masks the depth

Fix a face `F` and the field `v_k = -M` for `k notin F`, `v_i = 0` for `i in F`, with `M = M(eta) >= M_0 > 0`. A face `G` splits as
`G_in = G cap F` and `G_out = G minus F`. We call `G` inner if `G_out` is empty, mixed if both parts are nonempty, and suppressed if
`G_in` is empty.

**Lemma 7.4a (rates of mixed faces).** Put `p = M_0/(M_0 + d - 1)`. For every mixed face `G`,

    p r_{G_in} / (|G_in| + 2 r_{G_in}/(p M_0))  <=  lambda_G(v)  <=  r_{G_in}.                       (7.2)

For every suppressed face, `lambda_G(v) >= M`. For every face, `lambda_E(v) <= lambda_F(v) = r_F`.

*Proof.* The upper bounds are Fact 7.2 (i), since `lambda_{G_in}(v) = r_{G_in}`. A suppressed face has
`lambda_G(v) = r_G + M`. For the lower bound in (7.2), `(A_G - diag v)^{-1}` is the Green matrix of the chain on `G` killed at
exit from `G` and at rate `M` on `G_out`. Its row sums are the mean killing times `E_x zeta`, and its Perron root is
`1/lambda_G(v)`, so `lambda_G(v) >= 1/max_x E_x zeta`, as in (13) of the cycle note. We bound `E_x zeta`. Since `V >= 0`, every
rate is at most `1`, so a state has total jump rate at most `d - 1`. At each visit to `G_out` the next event is a killing
with probability at least `p`. Hence a sojourn in `G_out` returns to `G_in` with probability at most `1 - p`, and its mean
length is at most `1/(p M_0)`. A sojourn in `G_in` lasts at most `M_{G_in}^exit` in mean. The number of sojourns in `G_in` is
dominated by a geometric variable of mean `1/p`. Wald's identity gives `E_x zeta <= (M_{G_in}^exit + 2/(p M_0))/p`, and (14) of
the cycle note gives `M_{G_in}^exit <= |G_in|/r_{G_in}`.

Note that (7.2) is a two-sided bound with constants that do not depend on `eta`. Hence a mixed face has the same depth as its
inner part, and its rate differs from `r_{G_in}` by a bounded factor only.

**Proposition 7.4 (strong suppression).** Let `F` be a face with `D(F) > 0` and `M >= M_0 > 0`.

(i) For every noncritical `h` in `(0, D(F))`, the winner is the restricted selection `W_F(h)`, which minimizes `(|G|, r_G)` over
the inner faces with `D(G) > h`. It is a global cycle contained in `F`.

(ii) If `W` is the restricted winner on a maximal interval and `D(W) < D(F)`, the interval ends at `D(W)`. Hence the transitions
of the winner below `D(F)` occur exactly at the depths of the cycles inside `F` that win at some height.

(iii) The last restricted winner `C*(F)` is a cycle with `D(C*(F)) = D(F)`. For `h > D(F)` every face has a divergent score,
no inner face `G` with `D(G) < D(F)` wins, and the height at which the winner leaves `F` is at least `D(F)`.

(iv) A suppressed face never wins at a height `h > 0`.

*Proof.* Take `h` in `(0, D(F))` noncritical. An inner face `G` has score `m_G + tau r_G`, which tends to `m_G` if `D(G) > h` and to
`+infinity` if `D(G) < h`. The face `C*` of the deepest level exists by Theorem D, so some inner face has a bounded score. A
suppressed face has score at least `tau M_0`, which diverges because `h > 0`. This proves (iv) for these heights. For a mixed
face, (7.2) gives `tau lambda_G(v) -> infinity` when `D(G_in) < h`. When `D(G_in) > h`, the mixed face has score at least
`m_G >= m_{G_in} + 1`, while `G_in` has score `m_{G_in} + o(1)`. So no mixed face wins. Among inner faces the argument of
Proposition 7.3 applies word for word. The minimizer of `(|G|, r_G)` among eligible inner faces contains a cycle of the same
depth by Theorem D, and minimal cardinality forces equality. This proves (i). For (ii), the restricted winner `W` stays
eligible up to `D(W)`, and above `D(W)` it diverges while `C*(F)` stays bounded, because `D(W) < h < D(F)`. For (iii), at a
height just below `D(F)` the eligible inner faces are those of depth `D(F)`, and the smallest is a cycle by Theorem D. Above
`D(F)`, inner faces have `tau r_G >= tau r_F -> infinity`, mixed faces have `tau lambda_G(v) >= c tau r_{G_in} >= c tau r_F` with
`c = p/(d+1)`, and `E` has `tau lambda_E(v) >= c tau r_F` too. A suppressed face has rate at least `M_0`, while `lambda_E(v) <= r_F`,
so its score exceeds that of `E` by a divergent amount. This proves (iv) above `D(F)`. An inner face `G` with `D(G) < D(F)` satisfies `r_G - lambda_E(v) >= r_G - r_F >= r_G/2` for small `eta`,
so its score exceeds that of `E` by a divergent amount. Finally, every inner face of depth `D(F)` has a bounded score below
`D(F)`, so the winner is inside `F` up to `D(F)`.

**Why the leaving height exceeds `D(F)`.** Above `D(F)` the comparison is between divergent scores. Write
`rho_G = lambda_G(v) - lambda_E(v) >= 0`. By Fact 7.2 (iii) the winner minimizes `m_G + tau rho_G`, and `E` has the bounded value
`d - 1`. So a face is eligible when `rho_G` is of smaller order than `e^{-h/eta}`. By (7.2) with `G = E`, `lambda_E(v)` lies between
`c r_F` and `r_F`, so it has depth exactly `D(F)`. The deepest inner faces have `rho_G = r_G - lambda_E(v)`, which is of order
`e^{-D(F)/eta}` only when `lambda_E(v) <= (1 - kappa) r_G` for some fixed `kappa > 0`. When the excursions out of `F` return to `F`
with exponentially small probability, `lambda_E(v) = r_F (1 + o(1))`. If moreover `r_{C*(F)} = r_F (1 + o(1))`, as when
`C*(F) = F`, then `rho_{C*(F)}` is of smaller order and `C*(F)` keeps winning above `D(F)`. Route T7-B computed the leaving
heights from the exact finite-`eta` scores at high precision. For `F = {1}` in (27) they are `3 + g` with `M = t^{-g}`, and the leaving height exceeds `D(F)` on all 370 faces tested at
`g = 2`. The gap `r_F - lambda_E(v)` is the return flux divided by `M`, so a larger `M` delays the exit further. A weak
`M = t^{g}` with `g > 0` acts only at heights above `g`, and below that height cycles outside `F` win (the early exits of T7-B).

**Decision on `M`.** A fixed `M` (or any `M` bounded below) is the right choice for Proposition 7.4, and it is the choice of the
protected design C-I1. Arrhenius growth of `M` changes nothing below `D(F)` and makes the masking worse. Arrhenius decay of `M`
lets the complement compete. No choice of `M` makes the leaving height equal `D(F)`. Hence the leaving height is not an
observable of `D(F)`, and suppression is kept only for Proposition 7.4.

## 3. A calibrated attraction design for the depth function

The masking comes from the lack of a face whose rate is known. The unperturbed path has one, namely `E` with `lambda_E(0) = 0`.
A field `v >= 0` keeps a usable version of it, since then `lambda_E(v) <= 0` by Fact 7.2 (ii). We therefore reward the target face
instead of killing its complement.

**Design.** For a face `G`, a fixed known constant `c > 0` and a real `gamma`, put

    v^{G,gamma} = c t^gamma 1_G,    that is v_i = c e^{-gamma/eta} for i in G and v_i = 0 otherwise.            (7.3)

The design needs three calibrated quantities. The first is the time unit, so that `h` (equivalently `T = e^{h/eta} log N`) is
known. The second is the field amplitude `c e^{-gamma/eta}` in the same units. The third is the labelling of the states. It needs
no rate of `Q`. Note that `A_G - diag(v^{G,gamma}) = A_G - c t^gamma I`, so

    lambda_G(v^{G,gamma}) = r_G - c t^gamma    exactly.                                              (7.4)

**Definition.** `tau(G) = sup{ gamma : G is the eventual winner under v^{G,gamma} at some noncritical height h > gamma }`, with
`sup of the empty set = -infinity`. The definition uses only the observable map `(h, v) -> winner`.

We need two lemmas. The first is a version of Theorem D for a chain with an added killing. The second is the strict growth of
depth along nested cycles, which is also the main step of (7b) and is proved in Section 4.

**Lemma 7.5 (depth with a calibrated killing).** Let `K` be a set of states, `gamma` real and `s = c t^gamma`. For a face `G` put
`D^K(G) = lim -eta log lambda_min(A_G + s 1_{G cap K})`. The limit exists, and

    D^K(G) = max{ D^K(C) : C subset G, C a global cycle of Q }.                                   (7.5)

Moreover `D^K(C) = D(C)` if `C cap K` is empty and `D^K(C) <= gamma` if `C subset K`.

*Proof.* Add a cemetery state `partial` with rates `s` from every state of `K` and rates `e^{-L/eta}` from `partial` to every
state, for some `L > 0`. When `gamma < 0` first rescale time by `e^{gamma/eta}` as in Section 1A of the cycle note, which shifts all
depths by the same constant and changes no cycle. The new chain is a finite family of rare transitions in the sense of
Catoni's Definition 2.1, since only the logarithmic order of each rate matters there, so the constant `c` is harmless. For
`G subset E` its killed matrix is `A_G + s 1_{G cap K}`, whatever `L` is. Theorem D of the cycle note, whose proof uses only
Catoni's Proposition 4.11 and the elementary bound (14), applies to this chain. It gives the existence of the limit and the identity
`D^K(G) = max D^K(C)` over the cycles `C` of the enlarged chain inside `G`. Each such `C` is a global cycle of `Q`. Indeed the two
chains agree until the killing time, so for `x != y` in `C`

    P_x(tau_{C^c} < tau_y)  <=  P^K_x(the enlarged chain leaves C or is killed before tau_y),

and the right side is exponentially small. Hence the maximum over enlarged cycles is at most the maximum over global cycles
of `Q` inside `G`. The reverse inequality holds because `D^K(C) <= D^K(G)` for every `C subset G`, by Fact 7.2 (i). This proves (7.5). If `C`
does not meet `K`, its killed matrix is `A_C`, so `D^K(C) = D(C)`. If `C subset K`, its killed matrix is `A_C + sI`, whose smallest
eigenvalue is `r_C + s >= s`, so `D^K(C) <= gamma`.

**Lemma 7.6 (laminarity).** Two global cycles are disjoint or nested. This is Proposition 2.4 of Cirillo, Nardi and Sohier
(2015), quoted in the cycle note, and it holds for Catoni's cycles without reversibility.

**Theorem 7.7 (depths from the attraction design).** Fix `c > 0`.

(a) For every proper face `G` and every real `gamma`, if `G` wins under `v^{G,gamma}` at some noncritical height `h > gamma`, then
`gamma <= D(G)`. Hence `tau(G) <= D(G)`.

(b) Let `C` be a global cycle and put `D^-(C) = max_{i in C} D(C minus {i})`, with `D^-(C) = -infinity` for a singleton. Then
`D^-(C) < D(C)`, and for every `gamma < D(C)` the cycle `C` is the eventual winner under `v^{C,gamma}` at every noncritical height in
`(max(gamma, D^-(C)), D(C))`. Hence `tau(C) = D(C)`.

(c) For every proper face `F`,

    D(F) = max_{G subset F} tau(G).                                                                (7.6)

*Proof of (a).* Suppose `gamma > D(G)`, or `gamma = D(G)` and `c < a_G`. By (7.4) and (21) of the cycle note,
`lambda_G(v) = r_G - c t^gamma = (a_G + o(1)) t^{D(G)}` in the first case and `(a_G - c + o(1)) t^gamma` in the second. In both
cases `lambda_G(v) > 0` and `e^{h/eta} lambda_G(v) -> +infinity` for every `h > gamma`. On the other side `v >= 0`, so `lambda_E(v) <= lambda_E(0) = 0` by Fact 7.2 (ii),
and `E` has score at most `d - 1`. Hence `G` loses at every `h > gamma`. So a win at some `h > gamma` forces `gamma <= D(G)`.

*Proof of (b).* The inequality `D^-(C) < D(C)` is Lemma 7.9 below, together with monotonicity of `D`. Write `s = c t^gamma` and fix a
noncritical `h` with `max(gamma, D^-(C)) < h < D(C)`. By (7.4) the score of `C` is `m_C + tau r_C - tau s`. Here `tau r_C -> 0`
because `h < D(C)`, and `tau s = c e^{(h - gamma)/eta} -> infinity` because `h > gamma`. So the score of `C` tends to `-infinity`. We
compare with the four other kinds of faces.

1. Faces disjoint from `C`. They carry no field, so their rate is `r_G > 0` and their score is at least `m_G >= 0`.
2. Proper subfaces `G` of `C`. By (7.4) for `G` as well, `lambda_G(v) - lambda_C(v) = r_G - r_C`. Since `G subset C minus {i}` for
   some `i`, `D(G) <= D^-(C) < h`, so `tau (r_G - r_C) >= tau r_G/2 -> infinity` for small `eta`.
3. Faces `G` that strictly contain `C`. Write `A_G - diag v = (A_G + s 1_{G minus C}) - sI`. Hence
   `lambda_C(v) - lambda_G(v) = r_C - lambda_min(A_G + s 1_{G minus C}) <= r_C`. So `tau (lambda_C - lambda_G) <= tau r_C -> 0`, while
   `m_G >= m_C + 1`. The face `E` is of this kind.
4. Mixed faces `G`, which meet `C` without containing it or being contained in it. The same identity gives
   `lambda_G(v) - lambda_C(v) = lambda_min(A_G + s 1_{G minus C}) - r_C`. We apply Lemma 7.5 with `K = G minus C`. A global cycle
   `C'` inside `G` that meets both `C` and `K` would be nested with `C` by Lemma 7.6. It cannot lie inside `C`, since it meets `K`, and
   it cannot contain `C`, since `C` is not inside `G`. So every cycle in (7.5) lies in `G cap C` or in `K`. In the first case its
   depth is at most `D(G cap C) <= D^-(C)`, because `G cap C` is a proper subset of `C`. In the second case its depth is at most
   `gamma`. Hence `D^K(G) <= max(D^-(C), gamma) < h`, so `lambda_min(A_G + s 1_K) >= e^{-h'/eta}` for some `h' < h` and all small `eta`.
   Since `r_C` is of smaller order than `e^{-h/eta}`, `tau (lambda_G(v) - lambda_C(v)) -> infinity`.

In each case the score difference with `C` tends to `+infinity` or is at least `1/2` for small `eta`. By Fact 7.1, `C` is the
eventual winner. The interval is nonempty because `max(gamma, D^-(C)) < D(C)`. Hence `C` wins above `gamma` for every
`gamma < D(C)`, so `tau(C) >= D(C)`, and (a) gives equality.

*Proof of (c).* For `G subset F`, (a) and monotonicity give `tau(G) <= D(G) <= D(F)`. By Theorem D there is a global cycle
`C subset F` with `D(C) = D(F)`, and (b) gives `tau(C) = D(C) = D(F)`.

**Remarks on Theorem 7.7.**

1. *What happens at `h = D(C)`.* For `gamma < D(C)` and `h > D(C)` the score of `C` still tends to `-infinity`, but the faces that
   contain `C` now compete through `tau (lambda_C - lambda_G)`, which can diverge. So `C` may or may not keep winning above `D(C)`.
   The theorem does not use the right end of the winning interval. It uses only the threshold in `gamma`, at which the sign of
   (7.4) changes.
2. *What happens at `gamma = D(C)`.* Then `lambda_C(v) = (a_C - c + o(1)) t^gamma`. If `c < a_C`, part (a) shows that `C` never wins
   above `gamma`. If `c > a_C`, the rate is negative of order `t^gamma` and the competition at `h = gamma + eta log x` is a finite
   window of lines, as in Section 2B of the cycle note. Whether `C` reaches its envelope depends on the slopes of its
   supersets, so we do not claim that the threshold in `c` equals `a_C`. Prefactors are taken from (7c) instead.
3. *Uniformity.* For each fixed `(gamma, c, h)` the statements hold for all sufficiently small `eta`, after `N -> infinity` at each
   such `eta`. Nothing is claimed for `eta = eta_N`.
4. *Noncycles.* A noncycle `G` may still win above some `gamma` (for instance in a window), but (a) bounds its threshold by
   `D(G)`. This is why (7.6) takes a maximum over all subfaces and needs no prior knowledge of which faces are cycles.

**Remark 7.8 (the boosted-singleton reference fails).** The coordinator proposed `v_i = q_i - c t^gamma` on one state `i`, so that
`lambda_{i}(v) = c t^gamma` exactly. This field needs the exact value of `q_i` at each `eta`, and it breaks every face that contains
`i` and another state. Indeed the row of `A_G - diag v` at `i` has diagonal `c t^gamma` and off-diagonal sum `q_{i, G minus i}`, so
the chain gains mass at `i` at rate `q_{i, G minus i} - c t^gamma`. For `G = {i, j}` the determinant is
`c t^gamma q_j - q_ij q_ji`, which is negative as soon as `q_ij q_ji / q_j` exceeds `c t^gamma`. Then `lambda_G(v) < 0` with
`|lambda_G(v)|` of order `q_ij q_ji / q_j`, and `G` wins at every height above that order. In (27) with `i = 1`, `gamma = 3`, `c = 1`, the
face `{1,2}` has `lambda = -t^2 (1 + o(1))`, which Part B of the script confirms. A reference built on a singleton therefore has
depth at most `Gamma(i)`, and the attraction (7.3) on the whole target face avoids the problem because it adds no internal
gain.

## 4. (7b) Cycles and the cycle tree from the depth function

**Lemma 7.9 (strict growth along nested cycles).** If `C'` and `C` are global cycles with `C'` strictly inside `C`, then
`D(C') < D(C)`. Consequently `D(S) < D(C)` for every nonempty proper subset `S` of a global cycle `C`.

*Proof.* By (14) of the cycle note and Theorem D, `D(B) = lim eta log M_B^exit` for every face `B`, where
`M_B^exit = max_x E_x tau_{B^c}`. Fix `z in C minus C'`. By the definition (7) of a cycle there is `alpha > 0` with
`P_w(tau_{C^c} < tau_y) <= e^{-alpha/eta}` for all distinct `w, y` in `C` and all small `eta`. For each `eta` choose `y in C'` with
`E_y tau_{C'^c} = M_{C'}^exit`. Start at `y` and cut the path into rounds. A round runs until the chain leaves `C'`, and then, if
it is at a state `w in C minus C'`, until it returns to `y` or leaves `C`. A round ends outside `C` only if the chain leaves `C'`
directly into `C^c`, which implies `tau_{C^c} < tau_z`, or if it leaves `C` from `w` before reaching `y`. So by the strong Markov
property each round ends outside `C` with probability at most `2 e^{-alpha/eta}`, and the rounds are independent and identically
distributed. Let `R` be the number of rounds up to the exit from `C`. Then `E R >= e^{alpha/eta}/2`. Each round lasts at least its
first part, whose mean is `M_{C'}^exit`, and `R` is a stopping time for the rounds. Wald's identity gives

    M_C^exit >= E_y tau_{C^c} >= E R * M_{C'}^exit >= (e^{alpha/eta}/2) M_{C'}^exit.

Hence `D(C) >= D(C') + alpha > D(C')`. For the second statement, Theorem D gives a cycle `C'' subset S` with `D(C'') = D(S)`, and
`C''` is strictly inside `C`.

This proof uses only the definition (7) and the bound (14). It does not use reversibility, so it closes the non-reversible
case that route T7-B left as a plan.

**Theorem 7.10 (cycles from depths).** For a nonempty proper face `C` the following are equivalent.

(i) `C` is a global Freidlin and Wentzell cycle.

(ii) `D(C') < D(C)` for every nonempty proper subset `C'` of `C`.

(iii) `|C| = 1`, or `D(C minus {i}) < D(C)` for every `i in C`.

Moreover `Gamma(C) = D(C)` for every cycle. Hence the depth function determines the set of global cycles, their depths, and
the cycle tree, namely the laminar family of cycles ordered by inclusion with root `E`. Depths increase strictly along every
branch of the tree.

*Proof.* (i) implies (ii) by Lemma 7.9. (ii) and (iii) are equivalent because `D` is monotone under inclusion, since
`r_C <= r_{C'}` when `C' subset C`. Suppose (ii) holds. Theorem D gives a cycle `C* subset C` with `D(C*) = D(C)`, and (ii) forbids
`C*` to be a proper subset, so `C* = C`. The identity `Gamma(C) = D(C)` is part of Theorem D. Laminarity is Lemma 7.6, and strict
growth along branches is Lemma 7.9.

No nondegeneracy hypothesis is needed. Ties between depths of different faces are allowed. They are harmless because the
cycles are Catoni's strict cycles, and Lemma 7.9 rules out ties along nested cycles.

**Ties.** The naive criterion does not fail, but its weak form does. Take three states with `U = (0,0,0)` and all saddles
`H_ij = 1`. Then `D({1}) = D({2}) = D({1,2}) = 1`. The set `{1,2}` is not a strict cycle, since its internal height equals its
boundary height, and (ii) rejects it. The weak criterion `D(C') <= D(C)` accepts every set and would call `{1,2}` a cycle. In (27)
the faces `{1,2,3}` and `{1,2,4}` tie in depth with the cycle `{1,2}` and are rejected for the same reason. Route T7-B checked the
equivalence of (i) and (ii) on 5675 matrices, reversible and non-reversible, with seven tied families and no disagreement.

**Reconstruction.** Theorem 7.7 (c) and Theorem 7.10 together give the following. The map `(h, v) -> eventual winner`, restricted
to the attraction fields (7.3), determines the depth of every face, the set of global cycles, their depths and the cycle tree.

## 5. (7c) Prefactors from critical windows

Fix a critical depth `gamma` and use the unperturbed path at `h = gamma + eta log x`. By (26) of the cycle note the limiting scores
are `J(G) = m_G + x a_G` when `D(G) = gamma` and `J(G) = m_G` when `D(G) > gamma`, with `E` among the latter. Faces with `D(G) < gamma`
have `J(G) = +infinity`. Suppose the lower envelope of these finitely many lines has a unique minimizer on each of the open
intervals `(x_k, x_{k+1})`, `k = 0, ..., L`, with `x_0 = 0 < x_1 < ... < x_L < x_{L+1} = infinity`, and write `G_k` for the winner on
the `k`-th interval. These winners and endpoints are observable by Section 2B of the cycle note.

**Theorem 7.11 (what the window reveals).** (i) `G_L` has depth greater than `gamma` and slope `0`. (ii) For `k = L, ..., 1`,

    alpha_{G_{k-1}} = alpha_{G_k} + (m_{G_k} - m_{G_{k-1}}) / x_k,       alpha_{G_L} = 0,                      (7.7)

where `alpha_G = a_G` if `D(G) = gamma` and `alpha_G = 0` if `D(G) > gamma`. So the endpoints and the dimensions determine `a_G` exactly
for every face of depth `gamma` on the envelope. (iii) For a face `G` of depth `gamma` that is not on the envelope, the observation
gives only `a_G >= sup_{x > 0} (env(x) - m_G)/x`, where `env` is the reconstructed envelope, and every value in that range
gives the same winners. Monotonicity adds `a_G <= a_{G'}` for `G' subset G` of the same depth.

*Proof.* As `x -> infinity` every line of positive slope tends to infinity, so the last piece is a flat line, that is a face of
depth larger than `gamma`. Such faces exist since `E` is one. Two consecutive pieces cross at `x_k`, so
`m_{G_{k-1}} + x_k alpha_{G_{k-1}} = m_{G_k} + x_k alpha_{G_k}`, which is (7.7). For (iii), a line `m_G + x a` stays above the envelope
for all `x` exactly when `a` is at least the stated supremum. The bound `a_G <= a_{G'}` follows from `r_G <= r_{G'}` and equal depths.

The reference in (7.7) is absolute because the flat line of `E` has slope exactly `0`, which comes from `lambda_E(0) = 0`. So no
calibrated field is needed for the envelope faces.

**The four-state example.** At `gamma = 3` in (27) the envelope is `{1,2}`, `{1,2,3}`, `E` with `x_1 = 3/4`, `x_2 = 3/2` and dimensions
`1, 2, 3`. Then (7.7) gives `a_123 = (3 - 2)/(3/2) = 2/3` and `a_12 = 2/3 + (2 - 1)/(3/4) = 2`. These are the values of (32). The face
`{1,2,4}` is never on the envelope. Part (iii) gives `a_124 >= 2/3`, the supremum `2/3` being attained on the whole middle
interval, and monotonicity gives `a_124 <= a_12 = 2`. So `a_12` and `a_123` are recovered and `a_124 = 2` is not.

**A calibrated field on a singleton.** It does not give a better reference. A field `v` changes the rate of `E` to a value in
`[-max v, 0]` that depends on `Q`, so the slope of `E` stops being known. The field also moves the lines of the depth-`gamma` faces
through the limiting quasi-stationary weights of the target state. In (27) every limiting matrix in (29) and (30) has a single
nonzero column, at state `1`, so all quasi-stationary laws of the depth-3 faces and the limit of `pi` sit at state `1`. A field
`c t^3` at state `1` shifts every window line, `E` included, by `-c x` and leaves the endpoints unchanged. A field `c t^3` at
another state changes no line at order `t^3`. Singletons have depth at most `2`, so their own lines are not in this window. Hence
in the test case a calibrated singleton field reveals neither an absolute reference beyond `E` nor the value of `a_124`. Whether
some other calibrated field separates `a_124` from `a_12` is open.

## 6. (7d) Reversibility

No step above uses reversibility. Theorem D is Catoni's Proposition 4.11 with the bound (14), and both are general. The
prefactor lemma (21) to (23) is general. Lemma 7.4a uses the Green matrix and Wald's identity. Lemma 7.5 applies Theorem D to a
chain with a cemetery, which is never reversible, so even in a reversible family the proof of Theorem 7.7 goes through the
general theorem. Lemma 7.6 is Catoni's laminarity. Lemma 7.9 uses only (7) and (14). Theorem 7.11 uses only (26). The
reversible energy description (10) and (18) of the cycle note is not used.

The one input to check is Fact 7.1, that is the controlled score law C-P3 for a non-symmetric `A_F - diag v`. The outline states
it with `lambda_min(S_F - diag v)`. Its proof uses the whole-face upper bound after a Perron tilt by the positive right vector
and a rounded interior lower bound from C-P1, and both are written for an irreducible killed support. So the non-reversible
version should only need the statement rewritten with the Perron root of `-(A_F - diag v)`. The first open implication for
non-reversible families is this rewriting of C-P3 in the draft. Note also that every face is strongly connected here, since all
rates are positive.

## 7. Computational check of Theorem 7.7

The script `04_attraction_check.py` computes the exact finite-`eta` scores (7.1) for all nonempty faces under the field (7.3),
with the matrices built from exact rationals at `t = 10^{-32}` and `t = 10^{-48}`. The rate `lambda_G(v)` is the smallest real
eigenvalue of `A_G - diag v`, found by Newton's method on the exact characteristic polynomial (Faddeev and LeVerrier over the
rationals, from `05_core.py`), started to the left of every eigenvalue so that it increases to the Perron eigenvalue, which can be
negative here. The threshold `gamma` is scanned on `k/2 + 1/4`, and the heights on `gamma + j/4 + 1/8`, so no height is within `1/8` of
`gamma` or of an integer depth. For every proper face `G` the script records the largest grid value of `gamma` at which `G` wins at
some sampled height above `gamma`. Theorem 7.7 predicts the value `D(G) - 1/4` for cycles, at most `D(G) - 1/4` for noncycles, and
`max_{G subset F} tau(G) + 1/4 = D(F)` for every face.

Results (archived in `04_attraction_output.txt`). Eleven cost matrices, 138 proper faces. They are example (27), example (34),
a reversible 3-state family with a deep singleton beside a 2-state cycle (`V_12 = V_21 = 1`, `V_13 = V_23 = 3`, `V_31 = V_32 = 5`,
cycle `{1,2}` of depth `3`, singleton `{3}` of depth `5`), the tied families F1 (two disjoint pair cycles of equal depth `4`) and F5
(two identical non-reversible blocks, cycles of equal depth `5`) of route T7-B, four random non-reversible and two random
reversible 4-state matrices (seed `20261024`, costs in `{0,...,4}`). The random families include a non-reversible 3-state cycle
of depth `4` and singletons of depth `0`.

1. Every global cycle `C` gives `tau(C) = D(C) - 1/4` on the grid, both at `t = 10^{-32}` and at `t = 10^{-48}`.
2. Every noncycle gives `tau <= D - 1/4` or never wins above `gamma`. 23 noncycles win somewhere above some `gamma`, all within
   the bound of Theorem 7.7 (a). In (27) the noncycle `{3,4}` reaches the bound, `tau = 7/4` with `D = 2`, which (a) allows.
3. `max_{G subset F} tau(G) + 1/4 = D(F)` for all 138 faces.
4. The two values of `t` give the same thresholds on every face. There are 0 violations in total.
5. In the deep-singleton family the unperturbed path never shows `{1,2}`, since the deeper singleton `{3}` wins below `5`, and
   suppressing state `3` masks `{1,2}` by the mechanism of Section 2 (we did not recompute that leaving height here). The
   attraction design reads `D({1,2}) = 3` directly.
6. Part B (Remark 7.8). With `v_1 = q_1 - t^3` in (27), `lambda_{1}(v) = t^3` exactly, but `lambda_{1,2}`, `lambda_{1,2,3}` and
   `lambda_E` all equal `-t^2 (1 + o(1))` at `t = 10^{-8}` and `10^{-12}`.

This is a finite check at two values of `t` and on a grid of `gamma` and `h`. It is not a proof. The proof is Theorem 7.7.

## 8. Status

Status: proved under a stated hypothesis. (7a) is proved with the calibrated attraction design (7.3) in place of suppression
(Theorem 7.7, needing a calibrated time unit, a calibrated field amplitude and labels). The suppression design of the targets
does not determine `D(F)`, and Proposition 7.4 records what it does give (obstruction found for that design). (7b) is proved
with no nondegeneracy (Theorem 7.10, with strictness along nested cycles proved in general by Lemma 7.9). (7c) is proved
(Theorem 7.11, `a_12 = 2` and `a_123 = 2/3` recovered, `a_124` only bounded in `[2/3, 2]`). (7d) needs no reversibility. The stated
hypothesis is the input Fact 7.1, that is the controlled score law C-P3 at fixed temperature with a full-support start. For
non-reversible families the first unresolved implication is that C-P3 holds as written with the Perron root of
`-(A_F - diag v)` in place of `lambda_min(S_F - diag v)`. Whether some calibrated field separates `a_124` from `a_12` is open.
