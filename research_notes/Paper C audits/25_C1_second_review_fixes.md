# 25. Paper C1, fixes after the second referee report (October 25, 2026)

Scope: section 3 of the plan `01_C1_plan_JTP.md` (hygiene and framing), item (S) (the exact
Bessel range), item (O4) (uniqueness of the crossing), and every finding of the referee report
other than O1, O2 and O3. The open-question sentences on O1 (discrete layer) and O3 (reducible
faces) stay in Section 9. O2 is not stated as open in the paper and is not touched.

Page counts: article build 64 pages (was 60), Springer build 71 (was 67). Abstract 242 words
(248 if each math group counts as a word), 1435 characters on one line.

## Mathematics added

**(O4) Uniqueness of the crossing. Closed.** Theorem 5.8(iv): for large N, D_N has exactly one
zero in [1, N^(1/3)]. New Lemma A.5 (`lem:derivative`): on compacts of a face with (H),
d/dT log P_N(n) = -J_F(n/N) + O(1/T) for T_1 <= T <= N^(1/3). Proof:
- T d/dT log P_N(n) = E(M-1) - sum_i hq_i E(n_i - m_i)/(1-hq_i) under the law on run counts
  proportional to the terms of Lemma 2.3.
- E(M-1) is the derivative at c = 0 of the convex function Upsilon(c) = log P^(c) - log P^(0),
  where P^(c) uses e^c A_F. Since H_{e^c}(t) = e^{c(k-1)} H(e^c t), Lemma 5.5 and Theorem 5.4 at
  time e^c T give Upsilon(c) = (k-1)c/2 + (e^c - 1) T <theta, alpha> + O(1/T) for |c| <= 1.
- Convexity with difference quotients at step 1/T gives E(M-1) = T <theta, alpha> + O(1). The
  other term is T <q, alpha> + O(T^2/N).

At every maximizer, n/N = alpha*_F + O(1/L) (Theorem 5.7), so both one-sided derivatives of
log M_F are -lambda_F + O(1/L). Those of D_N are then delta + O(1/L) > 0 on the window where
every zero lies. So D_N is strictly increasing there.

The route closes with error O(1/T), not the O(1/T^2) of the plan. Only positivity is needed, so
O(1/T) suffices. The envelope theorem is replaced by one-sided derivatives of a finite maximum,
since M_F is a maximum over lattice points.

**(S) The exact Bessel range. Proved.** Proposition 6.2 (`prop:layer-cubic`, kept and
generalized). Put r_beta(eps) = Jbar_F(beta, eps^2) - q_i eps^2 - J_G(beta) + 2 sqrt(omega) eps -
(gamma - q_i) eps^2. Then:
- (a) r_beta is analytic, with r_beta = varkappa eps^3 + O(eps^4).
- (b) log f_F/(f_G B) = -S r_beta(sqrt(x/S)) + O(1/T + sqrt(x/T)), uniformly for 0 < x <= delta T.
  This sharpens the old O(sqrt(x/T) + x^2/T). The proof is the old one without truncating at
  order 3, plus Theorem 6.1(b) for x <= 1.
- (c) pi_in = pi_out gives r_beta = 0.
- (d) For fixed beta with first nonzero coefficient of order m, the ratio tends to 1 if and only if
  x = o(T^(1-2/m)). If r_beta = 0, x = o(T) suffices.
- (e) The cycle at beta = (1/2, 1/2): varkappa = -49/(64 sqrt(omega)), so m = 3.

New Proposition 6.6(v): J_G(beta, .) is affine on [0, infinity) if and only if pi_in = pi_out.
- Forward: grad P vanishes at psi_0, so psi_0 maximizes Psi - zP for every real z >= 0.
- Converse: d^2 J/dz^2 = 0 gives gamma = q_i, and the resistance vanishes.

Theorem 6.1(c) now holds for every beta with pi_in = pi_out, with c_1 = d/dz log C_G(beta, 0). The
proof was already verbatim. The abstract, the introduction and the remark after the theorem now
put the dividing line at pi_in = pi_out, not at reversibility.

The reviewer's 4-state example is in the paper after Proposition 6.2, and verify_layer.py part L
checks it. The facet is the cycle with rates 2 and 1, and a fourth state is joined to each of its
states by rate c both ways. I checked it myself:
- At uniform beta: r_beta is proportional to 1, so pi_in = pi_out = uniform and gamma = q_4.
- J_G(beta, z) is affine on [0, 0.5], with second differences 1.3e-15 and slope -omega = -6.75
  for c = 1.5.
- At beta = (0.2, 0.3, 0.5) the laws differ by 0.033 and J_G is not affine.

Not proved: whether r_beta = 0 forces pi_in = pi_out. It is added to the open questions.

## Claims and hypotheses (major claim C1-F1 and claim item 2)

- **Boundary layer.** It is now called the occupation density of the continuous-time chain in the
  abstract, introduction Section 1.2 (retitled), the opening of Section 6, the README and the
  cover letter. The counts near a facet are open, except the complete graph near a vertex
  (Section 8).
- **Local law.** (H) and compact subsets of the open face are restored in the abstract.
- **Crossings.** Delta >= 1 and delta > 0 are restored in the abstract and the cover letter.
- **Mode changes.** The sentence is dropped from the abstract. In the introduction and the cover
  letter it keeps symmetric support or full start support.
- **Balancing.** The uniform start is restored in the abstract. The counterexample is now in the
  introduction, after Theorem C. I checked it by exact enumeration (d = 2, N = 4, start in
  state 1): (3,1), (2,2), (1,3) have the probabilities 63/57/49 over 512 at T = 1/2, 15/13/9 over
  64 at T = 1, and 165/147/75 over 512 at T = 3/2, so (3,1) is the unique maximizer. At T = 2
  (3,1) and (2,2) tie. verify_complete.py part B checks this.
- **The 49/64 term.** The abstract no longer names it. The introduction names the specific cycle
  (rates 2 one way and 1 the other), and Proposition 6.2(e) keeps beta = (1/2, 1/2).
- **The complete graph.** "Makes about T switches" is gone. Theorem C(i) now says "the
  probability T/N of a switch to a given state". Theorem C is flagged as recovered from preprint
  B, in its header and in the paragraph before it, and it is presented as a worked example.

## Overlap with preprint B

The paragraph is replaced by Table 1 (`tab:overlap`), with the columns item of B, result here,
part covered and method. It sits under the same `\ifarxivbuild` wording (`\Bversion`). Rows:
Prop 2.2, Thm 3.1, Thm 3.2, Thm 3.3, Lemma 3.5 with Prop 3.6, Thm 3.8, Cor 3.9, Ex 3.10, Lemma 6.1
and Thm 6.4.

The table fixes the old inconsistency. Thm 3.2 is "all but the term 1/(8T) and the third-order
expansion", and Thm 3.3 is "the local law (7), not the root (8)". The items not reproved are
listed once, before the table: Prop 2.1, Prop 3.7, Sections 4 and 5, Thm 6.2, Remark 6.3 and
Appendix C. Section 7 points to the table. The README and the cover letter now describe the table.

## Positioning (no new citations)

New paragraphs in the related work:
- Fixed-chain large deviations (Miller, Ney and Nummelin, Kontoyiannis and Meyn, Herve and
  Ledoux). These cover a fixed matrix, while here the gap T/N tends to 0. Theorem 5.4 is an exact
  local estimate for the killed continuous-time occupation times, with its constant. The sentence
  "we found no statement ... that covers it" is a bounded claim. Lemma 5.5 transfers it.
- Brydges, van der Hofstad and Konig. Their density on the event that the range is F is
  Lemma 2.4, mixed over the start. Theorem 5.4 gives its exact asymptotics.
- Huang, Kious, Sidoravicius and Tarres. Symmetric rates, with one Bessel factor per edge, and
  the last exit tree and the cycling numbers.
- Pedler and Kovchegov, Meredith and Nir. Exact formulas for a fixed chain, while the layer
  kernel is an asymptotic form.
- Stadje. One nearly absorbing state, with exit probabilities of order 1/N, while here every row
  degenerates.

All these works were already in the bibliography. I checked each claim against a primary source:
- Crossref metadata and abstracts: BHK 10.1214/009171906000001024, HKST 10.1214/18-ECP194,
  KMN 10.1016/j.spl.2009.09.018, Stadje 10.1006/jmva.1999.1814, Kontoyiannis and Meyn
  10.1214/aoap/1042765670, Herve and Ledoux 10.1016/j.spl.2013.05.032.
- The HKST theorem itself (arXiv 1803.06930, via ar5iv), and the KMN arXiv abstract (0812.1775).
- Stadje's abstract on RePEc.

## Local fixes

- **Proposition 5.12(ii).** chi(alpha, 0) now carries the product of the theta_i for i >= 2.
- **Proposition 5.12(iii).** This proof cited a single-word bound that Lemma 5.5 does not
  contain. It now proves Upsilon(1) <= CT directly:
  - the upper bound for H_e has a constant continuous on the parameter set;
  - the lower bound uses one walk of at most 2k - 1 letters along a spanning tree;
  - the walk has weight at least mu_* min(1, w_*^2/R)^(2k-2), and the time factors are at least
    min(1, eps_0)^(k-1)/(k-1)!.
- **Lemma 3.2.** The second and third claims are now stated under "Now let Q be irreducible",
  with the counterexample q12 = 1, q21 = 0 after the lemma. paperC2 cites this lemma only for
  irreducible G.
- **Conductances.** kappa is now "twice those of the additive reversibilization".
- **Section 9 (scripts).** It now says which script computes the law two ways, that
  verify_rate_flows computes no law, and what verify_complete checks. It also says that no script
  checks Theorem 7.4(ii), (iii) or Corollary 7.6 at large N.
- **New script verify_complete.py.** Exact rational checks of:
  - Theorem 7.5 for d = 2, 3, 4 and small N, on a grid of p;
  - the counterexample above;
  - Theorem 7.4(i), with the coefficients, the monotone root and p_{k,k};
  - Remark 7.7.
- **verify_layer.py part L.** Added. Both are in verify_all.py.

## Framing

- The introduction now opens with the degenerating chain and the local law as a theorem about its
  occupation measure. Support selection comes second and the complete graph third, as "An
  example, the complete graph".
- There are no folder names or Kagey framing on the first two pages. Kagey appears only in the
  acknowledgments.
- An organization paragraph says that Section 4 uses Section 5, whose proofs do not use
  Section 4. This answers the referee's point on section order without moving sections, so that
  exported numbers do not move.
- Section 6 now states Theorem 6.1 and Proposition 6.2 right after the setting (new Section 6.2,
  "The main results"), with a three-step strategy paragraph. The proofs are in the new
  Section 6.8. The generalized kernel is defined in the setting, from the holomorphic extensions
  of Theorem 6.8, at any radius below 2 z_0.
- The "at every N" material is shorter. The intro sentence is cut, and Theorem C now gives the
  start-state counterexample instead. The window theorem's proof of (ii) and its consequence
  paragraph are condensed, and its statement is unchanged.
- The journal version is self-contained. No appendix is replaced by a citation.

## Numbers (EXPORTS.md has a dated note)

Interface and all exported numbers of Sections 2 to 5 and the appendices are unchanged, checked
against the .aux of both builds. This includes eq:A-radii, still (28) in the article build and A3
in the Springer build.

Moved in Section 6:

| Label | Now | Was |
|---|---|---|
| `thm:layer` | 6.1 | 6.9 |
| `prop:layer-cubic` | 6.2 | 6.10 |
| `thm:L-facet` | 6.8 | 6.6 |
| `lem:L-two` | 6.9 | 6.7 |
| `lem:critical` | 6.10 | 6.8 |
| `lem:layer-exact` (unexported) | 6.3 | 6.1 |
| `lem:layer-exact-discrete` (unexported) | 6.4 | 6.2 |
| `prop:pair-face` (unexported) | 6.5 | 6.3 |
| `prop:layer-constants` (unexported) | 6.6 | 6.4 |
| `prop:layer-prefactor` (unexported) | 6.7 | 6.5 |

paperC2 cites none of them. New labels: `lem:derivative` (Lemma A.5), `tab:overlap` (Table 1),
`sec:layer-main` and `sec:layer-proofs`.

## Checks

- Both builds settle after three passes, with no undefined or multiply defined references and no
  overfull boxes. The Springer log has one hyperref bookmark-level warning from the class's
  backmatter headings, which is not a reference warning.
- `py -I verify_all.py --quick` passes, 7 of 7 scripts in 226 s. The outputs in data/ are fresh.
- The aux files and __pycache__ are deleted.

## Not done, or only in part

- The notation group of the report (overloaded letters, symbols before definition) was handled
  only where it touched the edits: the switch counts, the generalized kernel and c_1. delta still
  means the exit-rate gap in Theorem 5.8 and a small multiple in Theorem 6.1, and S still means
  both the facet time and the polynomial S_n of Section 7.
- Sections 4 and 5 were not reordered (see Framing).
- The window theorem was condensed, not cut.
