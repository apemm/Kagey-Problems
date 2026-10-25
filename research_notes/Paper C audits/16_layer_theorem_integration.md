# Paper C audit 16: the facet theorem for every face, integrated into Paper C1

October 24, 2026. The local law of the weighted facet chain (formerly Hypothesis L, then the open
problem of Remark 6.8, `rem:layer-four`) is proved in `research_notes/C theorems 5 and 7/09_hypL_complex_laplace.md`
and audited in items 11 and 12 of that folder. This pass writes the proof into
`kagey-problems/problem131/paperC` and removes the restriction of the facet theorem to faces with
at most three states. Write scope was `paperC` and this note.

## Where each piece went

| Proof note | Paper | Label | Number (both builds) |
|---|---|---|---|
| Lemma 2.1 (Gaussian integral, branch) | paragraph before Lemma B.3 in `app_laplace.tex` | none | |
| Lemma 2.2 (complex Hessian Laplace lemma) | `app_laplace.tex`, after Remark B.2 | `lem:laplace-complex` | Lemma B.3 |
| Lemma 3.1 (torus, complex weights, general end vector) | `app_torus.tex`, after Lemma A.2 | `lem:torus-complex` | Lemma A.3 |
| (F2), (F4), (F5) for other weights, and the editor's item 1 | `app_torus.tex`, after the proof of Theorem 5.4 | `lem:local-general` | Lemma A.4 |
| Facts (F1) to (F4) at z = 0 | (P1) to (P4) in `sec_boundary.tex` | none | |
| Lemma 4.1 (complex critical point) | `sec_boundary.tex` | `lem:critical` | Lemma 6.8 |
| Theorem 5.1 (Hypothesis L) | `sec_boundary.tex` | `thm:L-facet` | Theorem 6.6, equation (19) |
| old Lemma 6.6 | kept as the closed forms | `lem:L-two` | Lemma 6.7 |
| facet theorem | restated for k >= 2 | `thm:layer` | Theorem 6.9 |

Lemma B.3 states the three changes to the proof of Lemma B.1 explicitly (the modulus of the complex
factor e^{T Psi(0)} in the localization, the bound |e^{-x^T J x/2}| = e^{-x^T (Re J) x/2} in the
integration, and the Gaussian integral with the continuous branch on the convex set S_m with
Hadamard's bound). Lemma A.3 follows the four steps of Lemma A.2 with a dominating nonnegative
system. Lemma 6.8(e) uses the audit's direct argument (defect D1): the nonnegative kernel vector
gives the Perron root 0, Lemma A.1 gives the gradient -pi, the critical equation forces pi = beta,
and stationarity plus convexity in log u identifies the tilt of Q_G(z). It does not cite
`prop:layer-constants`. The proof of Theorem 6.6 follows Theorem 5.1 of the note: the torus at
the radii |zeta_j| rotated by arg zeta_j, no separate contour shift, constants inherited by uniform
continuity on K x {|z| <= z_1/2} x T^m, with z_0 chosen last. Defect D2: the statement now says
that z_0 is a positive number, not given explicitly, depending only on Q, mu, i and K. A sentence
after the statement says why. A one-line remark after the proof records that the irreducibility
of F is not used.

## The theorem as it now reads

Theorem 6.6 (the weighted facet chain). Let G satisfy (H) with |G| = k-1 >= 1, let i not in G
with F = G u {i} irreducible, and let K in the open simplex of G be compact. There are a number
z_0 > 0, not given explicitly, and a constant C, both depending only on Q, mu, i and K, and
functions J_G(beta, z) and C_G(beta, z) on K x {|z| < 2 z_0}, holomorphic in z, jointly
continuous, real for real z, equal to the rate and the local-law constant of Section 6.1 for real
0 <= z < 2 z_0, and with C_G(beta, 0) = C_G(beta) > 0, such that uniformly for beta in K, S >= 1
and complex |z| <= z_0,
f^(z)_G(S beta) = S^{-(k-2)/2} C_G(beta, z) e^{-S J_G(beta, z)} (1 + eps), |eps| <= C/S.
For |G| = 1 this holds with eps = 0.

Theorem 6.9 (the facet layer) now reads "Let F be irreducible with k = |F| >= 2", with parts (a)
to (c) unchanged.

## Restriction removed

Abstract (both main files), Section 1.3 of the introduction, the opening of Section 6, the end of
Section 5.2, the paragraph after the proof of Theorem 6.9, Section 9 (first paragraph, the scripts
paragraph and the open questions), README, cover letter, TEMPLATE. Remark 6.8 is deleted. The
open-problems paragraph of Section 6 keeps only the discrete form of the facet theorem. Searches
for "three states", "at most three", "two or three", "hypothesis", "open problem" and
"layer-four" over the `.tex` and `.md` files of `paperC` leave only unrelated hits (the hypotheses
of Lemma B.1, "the hypothesis mu(F) > 0", "the arc of three states", the Lean hypothesis in README,
the history paragraphs).

## The editor's two open items (audit 13, section 7)

1. Lemma 6.6 (now 6.7) identified its constant with Section 6.1 through a local law with a general
   end vector that Remark 6.8 only sketched. Lemma A.4 now states and proves that local law for any
   nonnegative zero-diagonal A with strongly connected graph and nonzero nonnegative start and end
   vectors, together with the identities of the proof of Theorem 5.4 that Lemma 6.8(e) needs. The
   last sentences of the proof of Lemma 6.7 cite it. Remark 6.8 no longer exists.
2. Equation (18). The text now derives it: Q_G(z) is reversible with respect to nu_G for real
   z >= 0 (proof of Proposition 6.4(iv)), so r and l do not move, Proposition 5.2(b) writes C_G(beta,z)
   through tree(c(z)) with c_{jj'}(z) = c_{jj'}(0) + z omega pi_j pi_{j'}, and the three terms are
   the derivatives of the start factor, the end factor and (1/2) log tree, the last by Kirchhoff's
   rule d log tree / d c_e = R_e. A closing sentence notes that the holomorphic C_G of Theorem 6.6
   has the same derivative.

## Script

`paperC/verify_layer_general.py`, listed in `verify_all.py` (honours `--full`, which adds S = 64),
referred to in Section 9 and at the end of Section 6. Two facets with four states: a facet of a
non-reversible face with five states (the chain of `12_hypL_audit_check.py`) and the path 1-2-3-4
with killing and a periodic jump chain (the chain (e) of `11_hypL_audit_check.py`). The word sum
is computed exactly by a recursion over the words (checked against direct enumeration up to length
9, agreement 1e-15), the prediction from the continued complex critical point. 22 assertions.

S |eps| at S = 4, 8, 16, 32:

| facet | z | values | ratios |
|---|---|---|---|
| five-state face | 0 | 0.43276 0.43588 0.43742 0.43819 | 1.0072 1.0035 1.0018 |
| five-state face | 0.08i | 0.43310 0.43611 0.43761 0.43836 | 1.0070 1.0034 1.0017 |
| five-state face | 0.1 e^{2 pi i/3} | 0.43940 0.44285 0.44452 0.44535 | 1.0078 1.0038 1.0019 |
| path | 0 | 0.51082 0.53166 0.54133 0.54520 | 1.0408 1.0182 1.0072 |
| path | 0.08i | 0.50962 0.53803 0.54903 0.55333 | 1.0558 1.0204 1.0078 |
| path | 0.1 e^{2 pi i/3} | 0.52349 0.57935 0.60275 0.60815 | 1.1067 1.0404 1.0090 |

The five-state values agree to all printed digits with the audit's independent script. Lemma
6.8(e) holds at z = 0 and 0.05 to 1e-10. Cancellation exponents at S = 32 are at most 3.95.

With `--full` (S = 64, about 4 minutes) the next values are 0.43857, 0.43873, 0.44577 (five-state
face, ratios 1.0009) and 0.54700, 0.55529, 0.61005 (path, ratios 1.0031 to 1.0035). The
cancellation exponent reaches 7.75 for the path at the complex z, which costs about 3.4 digits and
is far below |eps|. The assertion bound on it is 10.

## Builds and scripts

Both main files built three times in `paperC` (the Springer one with
`TEXINPUTS=".;../common/sn-jnl;"`). No errors, no undefined references, no multiply defined
labels, no overfull boxes. Article 70 pages (was 65), Springer 77 (was 72). All exported numbers
in EXPORTS.md are unchanged, checked against both `.aux` files. `py -I verify_all.py --quick`
passed 8 of 8 scripts in 567 s. The auxiliary files were deleted and both PDFs kept.

## Not done

Nothing in the task list was left out. The paperC2 source still needs to re-sync from EXPORTS.md
(outside this folder). The new script is not interval-certified, like the others.
