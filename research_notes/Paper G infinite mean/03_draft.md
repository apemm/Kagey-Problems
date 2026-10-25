# Paper G: the draft

2026-10-25. The draft is in `kagey-problems/problem131/paperG`, written from `01_report.md` and
restricted to what `02_audit.md` confirms.

Title: "A local Lamperti law for the occupation count of a lattice Lévy walk with infinite-mean runs".
Class `ejpecp` (EJP, preprint mode), 27 pages. The build is clean, with no undefined or multiply defined
references and no overfull boxes. The only warning (`pagebackref`) comes from the class.

## What is in the paper

| Report item | Paper | Hypotheses as stated |
|---|---|---|
| Thm 1 (local law, one point iff compacts iff SRT for both laws) | Theorem A `thm:local`, Cor `cor:local-cases` | (RV), (SPAN), fresh start |
| Limit = Lamperti's density (Laplace transform, Stieltjes inversion) | Prop `prop:lambda` | none |
| Thm 4(a) shape, U iff cos(pi alpha/2) >= alpha | Theorem B `thm:shape` | b = 1 |
| Thm 2(a) fixed-j layer | Theorem C(a) `thm:ends` | (RV), (SPAN) |
| Thm 2(b), 2(c), Cor 2.3 | Theorem C(b), (c), Cor `cor:mode` | (LB+) and (SRT-) for (b), (LB±) for (c) and the mode |
| Missing lemma M0 | Remark `rem:M0` | |
| Thm 3(a) to (f) | Theorem D `thm:initial` (a) to (f) | (SRT±) in the header, (LB±) inside (c) and (d), (f) under (RV) only |
| Thm 3(g) aging-type start | Conjecture `rem:aging`, with the missing near-diagonal bound named | (LB±) added |
| Thm 4(b) lower bound | Theorem `thm:signs` | end value at j = 0 defined as lim Q(N)/T(N), assumed to exist |
| Exact count | Conjecture `conj:count` with the two missing lemmas | |
| Remark 2.4 (mass near the ends) | inside Remark `rem:global` | (SRT±) |

The audit's minor points are all applied: continuity of Lambda before the inversion, (LB±) written
into the hypotheses of (c) and (d), the j = 0 end value in the sign-change theorem.

## Added beyond the report

Each is a short consequence of audited steps, and each is listed in the README for the author to
check.

- Corollary `cor:lower`. Under (RV) and (SPAN) alone, liminf (N P_N(k) - L(k/N)) >= 0 uniformly on
  compacts, and if either SRT fails the limsup exceeds L at every interior point. The proof is the
  nonnegativity step of the audited necessity argument.
- Proposition `prop:pitchfork`. The minima split from 1/2 like sqrt(alpha - alpha_c), with the
  explicit constant. Checked numerically in `verify_shape.py`.
- The local law for the position W_N = 2A_N - N, and the match of (1/2)L((1+xi)/2) with
  Zaburdaev-Denisov-Klafter Eq. (61), checked by hand.
- Appendix A. Proofs of the dyadic sums (R4), of a_{m_N(t)}/N -> t^{1/alpha}, of the Poisson
  integral limit, and of the normalization of the minus sums.
- Figure 1 (Lamperti densities across the threshold, and the exact law at N = 2000 on a log scale).

## Literature, as far as verified

- Margolin and Barkai, arXiv cond-mat/0504454, Section III: "The transition between the U shape
  behavior and the W shape behavior happens at theta_c = 0.5946...". No derivation in that version.
  Journal reference from Crossref: J. Stat. Phys. 122 (2006) 137-167, DOI 10.1007/s10955-005-8076-9.
  The closed form cos(pi alpha/2) = alpha gives 0.594611644056836, consistent with their value.
- Zaburdaev, Denisov and Klafter, RMP 87 (2015), arXiv 1410.5100, Section II.A.3: the ballistic
  propagator is U-shaped and "for gamma >~ 0.6 the shape is W-like". Eqs. (61) and (83) give the
  Lamperti density.
- Mitov and Yanev, Adv. Appl. Probab. 33(4) (2001) 896-911, DOI 10.1239/aap/1011994035. From
  Crossref and the abstract only. Occupation-time process of alternating renewal processes in the
  infinite mean case, extending Dynkin, Lamperti and Erickson for the spent lifetime.
- Starreveld, Bekker and Mandjes, J. Appl. Probab. 55(4) (2018) 1287-1308, DOI 10.1017/jpr.2018.86.
- Lamperti 1958 not read in the original. The paper only names his theorem and the density.

## Computations

`py -I verify_all.py` passes (4 scripts, about 45 s). The scripts are new, adapted from
`lamperti_exact.py` and `initial_run.py` with a shared module `lamperti_law.py`.

- Ratios at alpha = 1/2: 1.0149, 1.0105, 1.0075 for N = 1000, 2000, 4000. All of Table 1 and Table 2
  are checked entry by entry.
- Sign changes 1, 1, 3, 5 at alpha = 0.3, 0.5, 0.7, 0.9, positions 104, 500, 896 (0.7, N = 1000) and
  1, 142, 2000, 3858, 3999 (0.9, N = 4000). Counts 1 at alpha = 0.58 and 3 at 0.61.
- U/W threshold 0.5946116441, critical-point counts on a grid, the transform eq:stieltjes in 30-digit
  arithmetic (error 2e-31), the double integral at alpha = 1/2 (5e-14).
- Identities against all sign strings for N <= 12, two different laws and a general initial run
  (1.1e-16).
- Initial run: 0.815, 0.836, 0.855, with (1 - ratio) N^0.2 constant to 5 percent. The scale-N start
  agrees with the conjectured formula (0.884, 1.299 at N = 2000 against 0.8694, 1.2732).

One check in the report's script did not carry over as first written. The residual of the defect
formula at N <= 2000 is dominated by the slowly decaying P(D >= eps N), so the check now tests that
the gap decays at the rate N^(-0.2) instead.

## Open items

See the list at the end of `paperG/README.md`: the Lamperti and Mitov-Yanev originals, the
Margolin-Barkai journal version, the Wang-Schulz-Deng-Barkai section numbers, citation details and MR
numbers, theorem numbers in the cited sources, the added results, whether to keep the aging
conjecture, and the page count (27 against 28 to 32).
