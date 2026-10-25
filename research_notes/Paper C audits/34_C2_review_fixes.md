# 34. C2 fixes after the review of October 25

This note records the changes to Paper C2 (`kagey-problems/problem131/paperC2`) made after the
review of the October 25 updates, section C2 and its issues DC2-F1 to DC2-F6.

Builds after the changes. The journal build `problem131_reconstruction.tex` has 40 pages (was 43)
and the arXiv build `problem131_reconstruction_arxiv.tex` has 46 pages (unchanged). Both build with
no warnings, no undefined references and no overfull boxes. `py -I verify_all.py` passes 6 of 6
scripts, and `verify_exactlaw.py` now has 72 checks (was 61). Statement numbers agree between the
2 builds.

## 1. The second moments without a cut (DC2-F1, DC2-F4)

The abstract said that the stationary law determines Q up to time reversal "when d <= 4, when Q has
no cut, and for generic Q, and then the second moments suffice". Read plainly, the last clause
covers the no-cut case, where it is false. Theorem 4.6 only claims the moments in cases (i) and
(iii).

We reproduced the counterexample with our own exact computation, in a simpler form than the one in
the review. Take 5 states, f = e1 - e2, f' = e3 - e4, g = (1,1,-1,-1,0), g' = (1,1,1,1,-4), which
are orthogonal to each other and to 1, J1 = f f'^T - f' f^T, J2 = g g'^T - g' g^T and
S = 10(1 1^T - 5I). Then

    Q = S + 5 J1 + J2,    Q' = S + 5 J1 - J2

have integer rates between 3 and 17 and the uniform stationary law. S commutes with J1 and J2, and
J1 J2 = J2 J1 = 0, so the symmetric part of Q^m only sees K^2 = 25 J1^2 + J2^2, which is the same for
Q'. Hence Sigma'_m = Sigma_m for every m, by hand. Exactly, Q has no cut (all 10 partitions 2|3),
Q' is neither Q nor Q^T, pi(Q - W)^n 1 agrees for n <= 4, and
pi(Q - W)^5 1 - pi(Q' - W)^5 1 = 8(w1 - w2)(w3 - w4)(w1 + w2 + w3 + w4 - 4 w5). K^2 is -100 on the
plane of f, f' and -80 on the plane of g, g', and S does not couple them, so it is exactly the
connectedness hypothesis of Theorem 4.5(ii) that fails. The minors of Q and Q' also differ, and the
stationary transforms differ at x = (1,...,5).

Changes.
- Abstract. "From the stationary start it determines Q up to time reversal when Q has no cut, and
  also when d <= 4 or Q is generic. In these last 2 cases the second moments already suffice, and
  without a cut they need not."
- Theorem B(iii) in the introduction now adds that in the second case the moments of order 1 and 2
  need not suffice, and the pointer after it cites the new remark.
- New Remark 4.7 (`rem:nocut-moments`, second moments without a cut), after the four-state
  paragraph that follows Theorem 4.6. It renumbers Section 4 from 4.7 on (Remark one-N is now 4.8,
  the gluing formula 4.9, the five-state example 4.15, the conjectures 4.16 and 4.17).
- Section 7. The open question "whether the stationary second moments of all orders always have
  the same fiber as the stationary law" is answered by the remark and is replaced by "which fibers
  the stationary second moments have when Q has no cut". The list of computed claims includes the
  absence of a cut and the fifth-order difference.
- `verify_exactlaw.py`, new part (5) with 10 checks: orthogonality, J1 J2 = J2 J1 = 0, the range of
  the rates, the stationary law, no cut, Q' not in {Q, Q^T}, Sigma_m for m = 1..8, the fifth-order
  difference, the spectrum of K^2, and that S does not couple the 2 eigenplanes.
- Cover letter, same correction.

## 2. The landing law in a memoryless block (DC2-F2)

The abstract and the cover letter described a memoryless block as left at a common rate and
entered in proportion to pi, without the common landing law. Definition 4.12 and the introduction
already had it. We checked the review's claim that the landing law is needed. In Example 4.15, let
states 1, 2, 3 jump to (4, 5) at rates (3/2, 3/2), (1, 2) and (1/2, 5/2). The exit rate is still 3,
the entries are unchanged and pi = (4,4,4,6,3)/21 is unchanged, and reversing inside B keeps pi. But
pi(Q - W)^4 1 changes by 2(w4 - w5)(w1 - 2 w2 + w3)/21, so the stationary laws differ.

Changes. The abstract and the cover letter now say "a block that every state leaves at one common
rate and with one common landing law, and that every jump enters in proportion to the stationary
law". The README describes Definition 4.12 the same way. The other statements of the definition
(sec_intro.tex and Definition 4.12) already had the landing law. We did not add the example to the
paper.

## 3. "Answered" (DC2-F3)

Only the generic start and the cases of Theorem 4.6 are answered. That the two reversals are the
only obstructions from the stationary start is Conjecture 4.16.

Changes.
- sec_intro.tex, first paragraph. "We answer the question for the second and the third resolution,
  also at low temperature. For the first we answer it from a generic start, and from the stationary
  start in a range of cases."
- sec_intro.tex, after Theorem B. "So the first level of the comparison is answered for a generic
  start, and for the stationary start in the cases of (iii)."
- sec_intro.tex, related work. "Ours include time reversal and the reversal of memoryless blocks
  (Theorem B), and we conjecture that from the stationary start there are no others (Conjecture
  4.16)."
- sec_exactlaw.tex, first sentence. "This section studies the question ..." in place of "answers".
- Cover letter, "We then study the exact law", and "the only further obstruction". README, the
  summary now says which levels are answered and which part is conjectural.

## 4. Minor items (DC2-F5, DC2-F6)

- One fixed N. The introduction said "one fixed N is not enough", which ignores the positive half of
  Remark 4.8. It now reads "At one fixed N >= 3, with N - 1 values of h, the counts still determine
  Q up to time reversal when d <= 4, and at N = 2 they can fail."
- The start e_1 in Example 4.15. The example now gives the 2 values, 4913/25716 for Q and
  48841/257160 for Q^[B] at x = (4,5,6,8,10), which we recomputed. Section 7 lists them among the
  computed claims, and `verify_exactlaw.py` checks them.

## 5. Length of the journal build

To bring the journal build from 43 to 40 pages without moving any main theorem, some proofs are
now full only in the arXiv build. In the journal build each is replaced by a sketch of 3 to 7
lines that names the steps and says that the details are in the arXiv version. All use the
existing `\ifarxivbuild` switch, so the arXiv build is unchanged apart from the review fixes, and
statement numbers agree in both builds.

- Proposition 3.9 (amplitudes), proof sketched.
- Remark 3.8, the written path reversal shortened to one sentence.
- Proposition 4.9 (gluing across a cut), proof sketched.
- Proposition 6.3 (prefactors), proof sketched. It is classical (Wentzell, Freidlin and Wentzell),
  as the text already says.
- Theorem 6.4 (critical windows), proof sketched.
- Examples 6.5 and 6.6, verifications sketched. Example 6.5 is also checked by the Lean module
  `CriticalWindow` and by `verify_cycles.py`.
- Lemmas 6.8 and 6.10 (laminarity, strict growth along nested cycles). They are standard (Catoni),
  and the journal now points to the sources and to the arXiv version.
- Theorem 6.14 (prefactors from window endpoints), proof sketched, and the discussion of Example
  6.5 after it shortened to its conclusion.
- Section 7, the list of Lean modules and the detailed description of `verify_exactlaw.py`
  shortened. The opening of Section 7 in the journal build now says that the sketched proofs are in
  the arXiv version.

The main theorems (A to D, Corollary 1.1 and the theorems of Section 4) keep full proofs in the
journal build. The cover letter no longer asks for extra length. It says which routine proofs are
sketched, and TEMPLATE.md and the README record the 40 pages and the list above.

## Files changed

`abstract.tex`, `sec_intro.tex`, `sec_minors.tex`, `sec_exactlaw.tex`, `sec_lowtemp.tex`,
`sec_verify.tex`, `verify_exactlaw.py`, `README.md`, `TEMPLATE.md`, `cover_letter.md`, the 2 PDFs and
the regenerated outputs in `data/`. Build files and `__pycache__` were removed.

## Not changed

The review's other C2 verdicts (every new result established, the low-temperature mechanism stated
correctly) needed no change. We did not test Conjectures 4.16 and 4.17 further.
