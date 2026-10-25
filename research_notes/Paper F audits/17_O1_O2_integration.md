# 17. Integration of the window (O2) and modes (O1) results into Paper F

October 25, 2026. Folder touched: `kagey-problems/problem131/paperF`, plus the page and
numbering lines of `kagey-problems/problem131/lean/PaperF/MAP.md` and the Paper F lines of
`kagey-problems/problem131/README.md`. Sources: `Paper F window O2/01_report.md`, `02_audit.md`,
`Paper F modes O1/01_report.md`, `02_report.md`, `03_audit.md`. Only what the audits confirm went
in, with their restrictions.

## 1. O2: the start of the zone (Section 4.5, `sec:window`)

- Theorem 4.13 (`thm:window`) is Theorem O2 (a) to (c). The Cramer exponent is written
  `\mathcal I_N(x)` and the threshold `\xi_N`, because `\Lambda_N` and `x_*` already name
  `a_-(N)` and the antimode constant in Section 6. The constant is `\varkappa_-`, the exponent
  `\beta_- = alpha_-/(alpha_- - 1)`.
- The lemmas are `lem:laplace` (Lemma 1 of the report, with the last claim of (iv), the limit of
  `a(m) theta_{u a(m)/m}`, stated and proved since (b) and Lemma 4 use it) and `lem:tilt`, which
  merges Lemmas 2 to 4 (part (a) the tilted local upper bound, part (b) the point lower bound
  with the Chebyshev window inside its proof). Scaling facts on `\mathcal I(m,d)` are
  `eq:I-scaling`.
- The proof of (c1) states the choice `X_N = K_1(eps) lambda_N` explicitly, as the audit asked,
  and joins Theorem B(b) beyond `K_1 lambda_N`. The estimate `-log(B_N G_N) = alpha_+ log(1/theta)(1+o(1))`
  is `eq:BG-log`.
- Wording follows the audit restriction. Nowhere does the paper say there is no window. The text
  after Theorem B, `rem:theta`, the introduction and the abstract say that the window shrinks to
  `K <= x <= (1+delta) xi_N`, that `P_N` is described there on the logarithmic scale, that the
  strip `(1 +- delta) xi_N` stays open, and that `rem:theta`'s question is settled
  (`xi_N = o(lambda_N)`, threshold sharp up to `1 +- delta`).
- The composite conjecture is the short Remark 4.14 (`rem:window-conj`), with the second-order
  tail condition and the first missing step.
- The remark after Theorem C(c) now says that `lambda_N` cannot be replaced by a constant and
  that Theorem 4.13 gives the sharp factor for fresh starts.
- No O2 numerics went into the paper (the audit calls them weak evidence for (c)).

## 2. O1: local extrema near the ends (Section 6.4, `sec:extrema`)

- Definitions: local maximum as a maximal constant block beating its neighbours, endpoints
  counted when they beat their one neighbour, plateaus counted once. End profile
  `\widetilde\kappa_+` and its limit `eq:profile-limit` (`prop:first-run` plus Theorem C(d)).
- `lem:diff-renewal` is Lemma 1 with the self-contained Wiener proof (truncation, weighted norm
  `eq:weighted`, product rule `eq:product-rule`, Neumann series). No Chover-Ney-Wainger citation.
  The sign typo of the audit is fixed (the series is `d * sum (d * t'')^{*k}`). Reference added:
  Wiener, Tauberian theorems, Ann. of Math. 33 (1932). The one-sided support of the inverse is
  argued in one sentence (continuity on the closed disk, analyticity inside).
- `lem:prep-diff` is Lemma 2. The side remark is corrected: `kappa_+ = 1/mu_-` on `j >= 1` only
  when `nu_- = T_-/mu_-` exactly. With only the asymptotic, the lemma says nothing more.
- `prop:copy` is fixed-window copying, plus a block version (b) that needs no no-ties hypothesis.
- `thm:modes-lower` is the lower bound `M_+ + M_- + 1`. Thanks to the block version the no-ties
  hypothesis of the report's Theorem 4 is dropped. The bulk criterion is automatic from
  `nu = o(T)`.
- `cor:four-modes` is the prepared-start link to Theorem C. 01 claims it proved (P6) and the
  audit does not contest Theorem 4 or Theorem C(d). The proof in the paper is by hand and slightly
  more general than P6: any strictly log-convex `f_-`, any fixed minus initial length `d_0 >= 2`
  with probability 1/2, fresh plus otherwise. It uses only `u_-(d_0) > 1/mu_-` (`lem:logconvex`).
- `lem:plus-diff` is (P0) to (P3) and `thm:first-diff` is M1 under (LD), the new named
  hypothesis `|f(n) - f(n+1)| = O(f(n)/n)` (added to Section 2.2). The M1 correction term is
  written `Delta C_w` with `C_w = C - 2 alpha_+ mu_+ w_- u_-`. The index typo of fact 4 is fixed
  (`[z^{j+1}]`).
- `thm:ends` is the fallback theorem (a) to (d), with (d) as a parity statement after deleting
  zeros of `D_N`. The clause on `j*_N` is stated only for the fresh plus start with
  `u_-(j) > 1/mu_-` for all `j >= 1`. In general the closed window contains every minimizer over
  `[J_+, N^{1-eta}]`.
- The criterion is `conj:three-modes` (exactly `M_+ + M_- + 1` modes, so three when each profile
  has one local maximum). The plan's "iff both profiles monotone" is not stated. The fair zeta
  start is quoted as showing that monotonicity is not the condition. M2 to M4 are named in one
  sentence each. The intro sentence "the number of local extrema inside the layers is not
  determined here" is replaced by a paragraph on what is proved.
- Not included: Lemma 5 of 01 (log-convex plus (LR) gives (LR2), not in the audit's verdict
  table), the zeta-on-runs->=2 bound of 15 modes (gaps not certified), the N = 186 four-mode
  counterexample (endpoint maxima, outside (RV)), Kwasnicki (only needed for the open M4).

## 3. A correction to the audited material

01 (section 4) says that for fresh starts "M_+ = 1 iff u_- is nonincreasing on j >= 1", and 03
says this checks for all three starts. It holds only for the plus start. For the minus start
`(0, u(1), u(2), ...)` has one local maximum whenever `u` rises and then falls, for example
`f(1) = 0.1`, `f(2) = 0.5` gives `u(1) = 0.1 < u(2) = 0.51`. For the fair start `f(1) = 0.6`,
`f(2) = 0.3` gives `u(1) = 0.6 > 1/2` and `u(2) = 0.66 > u(1)`, again one local maximum with a
nonmonotone `u`. The paper states the equivalence only for the fresh plus start.

## 4. Numerics

New script `verify_modes.py` (LF, output `data/verify_modes_output.txt` with sha256 header,
listed in `verify_all.py`). It checks the numbers now quoted in Section 7:
- `(u(j)-u(j-1)) mu^2/T(j) = -0.963, -0.996, -0.9996` at `j = 10, 100, 1000`.
- the M1 error at `j = 20`: 0.73 at N = 1000, 0.23 at N = 3000 (ratio 3.24).
- the fair zeta start: modes exactly at `k = 1, N/2, N-1` for N = 400, 1000.
- `cor:four-modes` with `d_0 = 5`: modes exactly at `k = 1, 499, 995, 1000` at N = 1000.
The modes are certified: every relative first difference exceeds twice the a priori rounding
bound of `certify_atlas.py`.

## 5. Abstract, length, build, checks

- Abstract 247 words (it was over 250 before this pass and was tightened). One sentence on O2,
  one on the proved part of O1, no theorem labels.
- 61 pages (52 before). Existing numbers unchanged (Prop 2.6, Remark 5.6, Theorem 6.1, Lemma A.1,
  Table 1). New: Section 4.5, Theorem 4.13, Remark 4.14, Lemmas 4.15, 4.16, Section 6.4, Lemmas
  6.5, 6.6, Proposition 6.7, Theorem 6.8, Corollary 6.9, Lemma 6.10, Theorems 6.11, 6.12,
  Conjecture 6.13.
- `pdflatex` three times: no errors, no undefined or multiply defined references, no overfull
  boxes. `py -I verify_all.py --quick`: 5 of 5 pass. `--full`: 7 of 7 pass. Aux files and
  `__pycache__` removed, PDF kept.
- `paperF/README.md` updated (status, the new statements, `verify_modes.py`, (LD)).
- `lean/PaperF/MAP.md`: `thm:inverse` is now Remark 5.6 in Section 5.7 of `sec_preparation.tex`,
  layout date and page count, and the list of unformalized statements (Sections 3 to 6 and
  Appendix A, (LD)). `problem131/README.md`: 61 pages and one sentence on the new results.

## 6. Points for a referee read

- `lem:laplace`(ii) cites the expansion inside the proof of `lem:stable`(i) at real argument.
- `lem:tilt`(a) uses (SPAN) through `|phi_0| < 1` away from 0 and a continuity argument in the tilt.
- The window lower bound in `thm:window`(a) relies on `lem:tilt`(b) with `d` within a factor
  `1 +- C/K` of `xB_N/p`, handled by monotonicity and `eq:I-scaling`.
- `thm:first-diff` IV uses `sum_m m b_m(j) <= j`.
