# 23. Referee report for the Journal of Theoretical Probability: Paper C1

Manuscript: "Occupation counts of rarely switching Markov chains: stratified local laws, support
selection and the boundary layer" (`kagey-problems/problem131/paperC/problem131_chains_sn.tex`,
Springer build, 65 pages). Report dated October 24, 2026. Numbers below are those of the Springer
build, taken from a fresh compilation.

I read the manuscript in order, section by section and appendix by appendix, before reading
`20_C1_deep_edit.md`. I then checked the seams that note names.

## 1. Summary of the paper

A chain on $d$ states runs for $N$ steps with transition matrix $I+(T/N)Q$, so it makes about $T$
switches, with $1\le T\le N^{1/3}$. The paper studies the law of the count vector $n$. The
results are:

- **Local law on a face (Theorems A, 5.4, 5.6, 5.7).** On each face $F$ that satisfies (H), and
  uniformly on compact subsets of the open face, $-\log P_N(n)=(k-1)\log N+TJ_V(n/N)-\frac{k-1}2\log
  T-\log C_F+O(1/T+T^2/N)$. $J_V$ is the Donsker–Varadhan functional of the whole chain, and its
  restriction to $\Delta_F$ equals the functional of the killed chain (Proposition 3.1). The
  constant $C_F$ is explicit, and in the reversible case it is a square root of a weighted tree
  count (Proposition 5.2). The face maxima are $M_F\sim N^{-(k-1)}T^{(k-1)/2}K_Fe^{-T\lambda_F}$,
  uniformly in a field, and uniformly over a compact class of reversible chains
  (Proposition 5.12).
- **Support selection (Theorems B, 4.2, 4.4, 5.8, 5.9).** When $T=\tau\log N$ the mode lies on a
  minimizer of $\tau\lambda_F+|F|-1$, and the winners can be read off a convex hull. A crossing
  between two (H) faces satisfies $\delta T+\frac\Delta2\log T=\Delta\log N-\log(K_F/K_G)+O(1/\log
  N)$, so the coefficient of $\log\log N$ is $\frac12$ universally. Tie windows are described. A
  reducible example (Example 5.11) has coefficients $1$ and $0$.
- **Boundary layer (Section 6).** Pulling the visits to $i$ out of the run expansion gives an exact
  contour representation (Lemmas 6.1 and 6.2). Pair faces have a closed Bessel form
  (Proposition 6.3). The facet expansion of the rate has a square-root singularity and an
  effective-resistance correction $\gamma_\beta$ (Proposition 6.4). The prefactors match for
  reversible $Q$ (Proposition 6.5). A local law for the weighted facet chain with a small complex
  parameter (Theorem 6.6) is proved on a torus through a complex critical point, with a Laplace
  lemma for a complex Hessian (Lemma B.3). The facet theorem (Theorem 6.9) has three parts: a
  generalized kernel with relative error $O(1/T)$; the Bessel kernel in logarithmic form; and, for
  reversible $Q$, the Bessel kernel in relative form with a first correction.
- **Complete graph and vertex (Sections 7 and 8).** For $Q=J-dI$ with the uniform start: each face
  crosses a vertex exactly once at every $N$, the face maxima are balanced when $T\le N/d$
  (log-concavity of Laguerre-type polynomials), and there is exactly one mode change for $T\le
  C\log N$. Near a vertex, a uniform root bracket holds for $T$ of order $\sqrt N$ (Theorem 8.2).

## 2. Recommendation: minor revision

I found no mathematical error. I checked every proof line by line. Where a claim could be checked
by recomputing a small case from the definitions, I did so, and it held: the constants of
Example 5.11, the 4-cycle and 3-path exponents, the counts in Remark 7.7, the facet constants
$\omega_\beta,\gamma_\beta$ of the non-reversible cycle, Corollary 5.3 for the pair, and the
complete-graph constants. The general facet local law has a delicate architecture: a torus at the
radii of a complex critical point, with no contour moved, and a Laplace lemma for a complex
symmetric Hessian whose real part is positive definite. That architecture is sound. The local law
and the crossing equation, with its universal $\frac12\log\log N$, are clean results that a
probabilist working on occupation measures or quasi-stationarity would cite. The revision I ask for
covers four things: two claims whose wording outruns what is proved (the non-reversible
restriction "is real" and "every change of the mode is located"), the positioning against the
classical literature on Markov-binomial laws with rare switching, and the organisation and scope of
a 65-page paper, part of which reproves the author's own preprint and part of which serves an
unpublished companion paper. None of these needs new mathematics beyond one short computation
(item M1).

## 3. Major concerns

**M1. The claim that the non-reversible restriction "is real" rests on numerics.** (Abstract;
Section 1.2; the paragraph after Theorem 6.9; Section 9.) The abstract says that without
reversibility the relative Bessel form holds only for $x$ up to order $T^{1/3}$, "and an example
shows this restriction is real". What the paper offers for this is three floating-point ratios,
19.6, 265 and 48268, at $x=T/20$ for one cycle. Two problems follow.

(a) Section 9 states that "no proof rests on a computation". The sentence in the abstract is a
mathematical claim, and as written it rests on one.

(b) The numerics show failure at $x\asymp T$. They do not show that the threshold $T^{1/3}$ is
sharp.

The remedy is short, and the paper already contains every ingredient. By Theorem 6.9(a) and the
saddle-point evaluation in its proof, $\mathbf K_\beta/\mathbf B_\beta=\exp\bigl(-\tfrac S6\partial_z^3J_G(\beta,0)z_*^3
+O(\sqrt{x/S}(1+x))\bigr)$ up to the second-order terms already displayed. So the claim follows
for $T^{1/3}\ll x\le\delta T$ once $\partial_z^3J_G(\beta,0)\ne0$ for the example. That
derivative can be computed in closed form by differentiating the critical equation of
Proposition 6.4(ii) once more. Alternatively, Proposition 6.4(i) gives $J_F$ exactly for the
two-state facet. I ask the author to state this as a proposition (or as part of the remark), with
the value of $\partial_z^3J_G$ for the cycle, and to keep the numbers only as an illustration. If
this is not done, the abstract and Section 1.2 should say "numerical evidence suggests", and
Section 9 should be qualified.

**M2. "We locate every change of the mode between irreducible faces up to $O(1/\log N)$" is not
proved as stated.** (Abstract; Section 1.1; Remark 5.10.) The body has three relevant results:

- Theorem 5.8 locates the zeros of $M_F=M_G$ for a given pair.
- Theorem 5.9 locates the changes in a tie window only up to $o(1)$ in $t$, through its part (i),
  which has error $O(\log L/L)$.
- Theorem 4.2(iii)–(iv) is stated for fixed $\tau$, not uniformly for $\tau$ in compact
  intervals between switch values.

Three steps are needed to assemble the claim, and none is written down:

1. A uniform-in-$\tau$ version of Theorem 4.2(iii). This is easy from the uniform bounds of 4.2(ii).
2. The observation that, near a kink of $E$ at which exactly two distinct lines meet, every global
   mode lies on a face of one of the two lines, so that a change of the mode is a zero of
   $D_N$ for that pair. Then Theorem 5.8(ii)–(iii) gives $O(1/L)$.
3. A treatment, or an explicit exclusion, of degenerate kinks where three or more distinct lines
   pass through one point.

I ask for a corollary that states this precisely, under the genericity hypothesis if it is needed.
The abstract should then match it. Remark 5.10 ("every change in a tie window is a crossing of
Theorem 5.8") would become that corollary.

**M3. Positioning against the classical rare-switching literature.** The regime of the paper, with
switch probabilities of order $T/N$, is the regime of Dobrushin's classical theorem for two-state
chains. Dobrushin classified the possible limit laws of the number of visits according to how the
transition probabilities scale with $n$; for switch probabilities of order $1/n$ the limit is
non-Gaussian. A substantial literature on the "Markov binomial" law grew from that paper, including
compound-Poisson and local approximations. The related-work section cites Pedler and Kovchegov,
Meredith and Nir for the two-state Bessel density, but it does not cite this line at all. A JTP
reader will ask how Theorem A at fixed $T$, the pair face of Proposition 6.3 and the $d=2$ case of
Theorem 7.4 compare with it. Please add the references in Section 5 below, and add two or three
sentences that say what is new relative to them: the $d$-state count vector, the uniformity in
$T$, the explicit constants and the face structure. The large deviation and local limit
literature for Markov additive processes (Ney–Nummelin; Miller's exact asymptotics for chains on a
finite state space) should also be placed next to Kontoyiannis–Meyn and Hervé–Ledoux, since the
paper's own description of its novelty ("for a killed chain whose switch probabilities shrink with
$N$") is made against that background.

**M4. Scope, overlap and organisation.** These are editorial points, but at 65 pages each one
matters.

(a) *Overlap with the author's preprint [paperB].* Sections 7 and 8 and Appendices C and D
reprove, or are cases of, results of arXiv:2610.09258v1. Remark 8.3, the sentence after
Theorem 7.4 and Example 7.2 also cite it for results that are not reproved. The journal build says
the paper "supersedes" the preprint. The editor should be told plainly, for instance in the cover
letter, which results of the preprint are new here and which are quoted. The paper itself should
have a single sentence or a short table that does the same. As it stands the reader has to collect
it from five places.

(b) *Material that serves an unpublished companion.* Proposition 5.12 fixes an ad hoc set of
fields, with $U=8R/b^2$ and $\bar v=4R+4UR^2$, "because it is the one used in [paperC2]". paperC2
is in preparation. A JTP referee cannot assess that use. Two remedies are possible: state
Proposition 5.12 for an arbitrary compact set of fields, or for an arbitrary compact class of
generators, which the proof already gives; or move it to the companion paper. The constants $U$
and $\bar v$ play no role in this paper.

(c) *Order of Sections 4 and 5.* Section 4 ("first-order selection") uses the local law and the
face maxima of Section 5 (see the sentence before Theorem 4.2). Theorem 4.2(i) is a weaker form of
Theorem 5.6. It would read more naturally, and save space, to put the local law first (the present
Sections 5.1–5.2) and derive first-order selection and the hull as consequences. Theorem 4.2(i)
could then be dropped. Part (ii) is the only part of Theorem 4.2 that does not follow from
Section 5, because it covers reducible faces.

(d) *Length.* After the recent cuts there is little literal repetition. The paper is still long
for its core contribution, mainly because it carries three strands: the general theory, the
complete graph and the near-vertex layer. I would not insist on further cuts beyond (b) and (c).

## 4. Minor concerns

1. **Abstract, "Near a facet of every face".** Theorem 6.9 requires $F$ irreducible and the facet
   $G=F\setminus\{i\}$ to satisfy (H), with $\beta$ in a compact subset of $\Delta_G^\circ$ and
   $x\le\delta T$. Please say "of every irreducible face whose facet satisfies (H)".
2. **Abstract, "for large $N$ the mode changes exactly once".** Corollary 7.6 and Theorem C(iii)
   restrict to $T\le C\log N$. The abstract should keep the restriction.
3. **After Theorem 5.8, "On the 4-cycle the explicit form in (iii) is still off by 0.06 at
   $N=10^{14}$".** The text does not say which crossing. From `verify_second_order.py` it is the
   vertex against the 3-arc, $T_N=42.2633$ against 42.2059. That pair never carries the mode
   (Section 4.1). For the vertex–pair and pair–cycle crossings, which do carry it, I compute gaps of
   0.035 and 0.087 between the explicit and implicit forms. Please name the pair, or use a pair
   that carries the mode.
4. **Overloaded notation.**
   - $G$ is the switching graph $G_F$, the second face in Theorem 5.8, the graph in Section 5.5,
     the facet in Section 6 and a generator in Appendix A.
   - $b$ is the rate in Example 5.11, the edge bound in Section 5.5, the function $b(z')$, the
     constant $b_\beta$ and the large count in Section 8. The proof of Proposition 5.12 has to warn
     the reader that "$b(z')$ is not the edge bound $b$".
   - $S$ is the point set of Theorem 4.4, the facet time, $S_n(u)$, $S_F$, the matrix $S$ of
     Section 5.5 and the diagonal $S$ of Appendix A.
   - $\Delta$ is the simplex $\Delta_F$, the size difference and $\Delta(x)$ in Appendix C. $V$ is
     the face $[d]$, $V_F$ and $V_N$. $J_F(s,x)$ in Section 6.4 reuses $J_F$.

   Renaming the facet (for example $F'$ or $E$) and the class-edge bound would remove most of the
   friction.
5. **Theorem 5.9(ii) and (iii).** The roles of $\varepsilon_0,\varepsilon_1,\varepsilon,t_0$ are
   clear only from the proof. A sentence saying that $\varepsilon$ and $t_0$ depend only on $Q$,
   $\mu$ and $\tau^*$ would help.
6. **Theorem 6.6.** $z_0$ is not explicit, and the paper says so. One sentence explaining why
   $z_0$ cannot be taken as large as the domain of $J_G(\beta,\cdot)$ would help the reader of
   Theorem 6.9, whose $\delta$ depends on it.
7. **Section 9, Computations.**
   - `verify_forest.py` is listed as checking "Sections 2 to 5 and 7". It in fact tests the
     general-face tree (forest) formula, which the paper no longer states (its docstring cites
     "Proposition 4.9 and Lemma A.3").
   - The scripts and their outputs label results by older numbers ("Theorem 4.4" for the local
     law, "Lemma 4.5", "Proposition 4.14" for Example 5.11, "Theorem 4.7" for the crossing).
   - The folder also holds `verify_sticky_fisher.py`, which is not part of the paper. Section 9
     says "7 scripts", which is right, but a reader opening the folder will count 8.

   Please align the labels with the published numbering and describe `verify_forest.py` correctly,
   or drop it from the list.
8. **`bib_switching.tex` ends with `\end{document}`.** The main files also end with
   `\end{document}`, which is never reached. This is harmless, but the editorial office's tools
   may object.
9. **Example 2.5(ii).** "One-dimensional $d$-state Potts chain with free boundaries" is apt. A
   reference for the Potts identification would help readers from statistical mechanics.
10. **Proposition 6.4(iii).** The proof passes from $O(\varepsilon^{1/2})$ to $O(\varepsilon)$ for
    $\psi^*-\psi_0$ in one sentence. This is fine, but it needs the uniform strict concavity of
    $\Psi_\beta$ on the bounded set modulo constants, which should be stated: unique maximiser plus
    compactness gives $\Psi_\beta(\psi_0)-\Psi_\beta(\psi)\ge c\min(|\psi-\psi_0|^2,1)$.
11. **Theorem 6.9(b), the case $x\le1$.** "In the same way the term $c_1z$ gives
    $O(z_*(1+1/\zeta))$" hides the interaction with the Gaussian factor. One more line would do.
12. **Section 1.4.** "Good's formulas (3) and (10) are our Lemmas 2.3 and 2.4" and the remarks
    after those lemmas say the same thing twice. Keep one.
13. **Title.** The title is accurate but long. "Occupation counts of rarely switching Markov chains:
    local laws on faces and support selection" would be shorter. "Boundary layer" is then carried
    by the abstract. This is the author's choice.
14. **Open questions (Section 9).** It would help to say whether uniqueness of the zero of $D_N$
    (Theorem 5.8) fails in any known example, or is only unproved.

## 5. Missing references

Each of these should be cited and positioned, as described under M3.

- R. L. Dobrushin, *Limit theorems for a Markov chain of two states*, Izv. Akad. Nauk SSSR Ser.
  Mat. **17** (1953), 291–330; English transl. in Selected Transl. Math. Statist. Probab. **1**
  (1961), 97–134. This is the classical classification of limit laws of occupation counts when the
  switch probabilities scale with $n$. It is the $d=2$ prototype of the regime of the paper.
- V. Čekanavičius and P. Vellaisamy, *Compound Poisson and signed compound Poisson approximations
  to the Markov binomial law*, Bernoulli **16** (2010), 1114–1136, doi:10.3150/09-BEJ246
  (arXiv:1011.5734). It gives local and total-variation bounds for the two-state count in the rare
  switching regime, and it reviews the Markov-binomial literature descending from Dobrushin.
- K. R. Gabriel, *The distribution of the number of successes in a sequence of dependent trials*,
  Biometrika **46** (1959), 454–460. This is the exact two-state ("Markov binomial") law. It
  belongs with Whittle, Dawson–Good and Goodman.
- P. Ney and E. Nummelin, *Markov additive processes I. Eigenvalue properties and limit theorems*
  and *II. Large deviations*, Ann. Probab. **15** (1987), 561–592 and 593–609. These are the
  standard references for the LDP and local limit theory of Markov additive processes, against
  which the paper defines its novelty.
- H. D. Miller, *A convexity property in the theory of random variables defined on a finite Markov
  chain*, Ann. Math. Statist. **32** (1961), 1260–1270. These are exact (Bahadur–Rao type) large
  deviation asymptotics for additive functionals of a finite chain, the fixed-chain analogue of
  the constant $C_F$.
- Optional, recent: *On the occupation measure of evolution models with vanishing mutations*,
  arXiv:2602.06829 (2026). It treats occupation measures under vanishing switching rates and
  belongs with Dietz–Sethuraman and Bouguet–Cloez in Section 1.4.

I verified the bibliographic data of Dobrushin (Izvestiya 17(4), 291–330, via Math-Net.ru) and of
Čekanavičius–Vellaisamy (Bernoulli 16(4), 1114–1136). I have not verified the other entries
against the journals: the translation page range for Dobrushin, Gabriel, Ney–Nummelin and Miller
are given from memory, and arXiv:2602.06829 was seen only in a search listing. The author should
check all of these before adding them. My search found no recent paper that proves a local law
for the full count vector of a $d$-state chain with switching of order $T/N$, nor one that treats
the modal support. The novelty claim appears to stand.

## 6. Questions for the author

1. Does the local law extend to $T$ up to $N^{1/2-\epsilon}$ with error $O(1/T+T^2/N)$? Lemma 5.5
   holds to $N^{1/2}$. Is $N^{1/3}$ needed only for the maximiser estimate in Theorem 5.7, as the
   proof indicates?
2. For a reducible face, is the conjectured power $(k^*-1)/2+k_F-k^*$ (Section 9) consistent with
   Example 5.11, where $M_{\{1,2\}}$ has power $T^1$ with $k_F=2$ and $k^*=1$? It is consistent,
   since $0+1=1$. If so, it would be worth saying that the example confirms the conjecture.
3. In Theorem 6.9(c), is $c_1(\beta)z_*I_0/I_1$ the full first correction, or does the
   second-order term of $C_G(\beta,z)$ contribute at the same order when $x\asymp1$?
4. Can the effective-resistance formula for $\gamma_\beta$ be related to the flow (level 2.5) rate
   of Bertini–Faggionato–Gabrielli? The authors cite that work, and a sentence here would
   strengthen the link to the Kim–Landim line.

## 7. Checks run, with results

**Builds.** I compiled both main files in a scratch copy of the folder, twice each.

- Springer build: 65 pages.
- Article build: 59 pages.
- Neither build has an undefined reference or citation or a multiply defined label.
- The only warning is a hyperref bookmark-level note.

**Seams after the cuts in note 20.**

- Nothing cites the removed general tree formula, Proposition 7.1, Corollary 7.2, Remark 7.4,
  Lemma A.5 or equation (21).
- No leftover symbols $S_{a,b}$, $u_N$, $z_N$, $c_0$ or `\arb` remain.
- The weighted Cayley lemma and Example 7.2 are used only in Section 7, and their proofs are
  self-contained.
- Example 5.11 now computes $K_{\{1,2,3\}}$ directly, and the computation is correct (see below).
- The only stale numbering is in the scripts and their outputs (minor point 7).

**Recomputations by hand or by my own scripts, independent of the paper's scripts.**

- *Example 5.11.* Three checks:
  - From Definition 5.1 (the optimal $r_\alpha$ by minimisation, then $\widehat Q_\alpha$,
    $Z_\alpha$ and $\Sigma_\alpha$), $K_{\{1,2,3\}}=(1+2b)^2/(2\sqrt3\pi b)$ and $\det\Sigma=3b^2/(1+2b)^4$
    hold at $b=2.5,3,5$ to $10^{-13}$.
  - Symbolically, the Hessian of $J_V=b\alpha_1+\alpha_2+\alpha_3-3(b\alpha_1\alpha_2\alpha_3)^{1/3}$
    in $(\alpha_2,\alpha_3)$ at $\alpha^*$ is exactly $\frac{1+2b}{3b}$ times the displayed matrix,
    with determinant $(1+2b)^4/(3b^2)$.
  - Parts (ii) and (iii), including the need for $b>2$ so that $\{1,2\}$ lies on the hull, check
    out by hand.
- *Constants and exponents.* The 3-path exponents $(3-\sqrt5)/2$ and its switch values 7.3 and 11.8
  at $N=90$ hold. So do the 4-cycle exit rates and switch values $\tau=1,2,1+\sqrt2$, and $K=1/\sqrt{2\pi}$
  for a 4-cycle pair (Corollary 5.3). The complete-graph constants $K_F=D_k/d$, $b_{FG}=a_k$, the
  values $a_2,a_3,a_4$, $a_2=\frac12\log(\pi/8)$, $e^{-(a_2-a_3)}=0.827$ and the formula
  $\Sigma_k=(2/k^2)(I-J/k)$ all hold.
- *Remark 7.7.* With $u=7/20$ and $T=14/17$, $S_{(2,2)}=4123/4000$ and $S_{(2,1,1)}=3969/4000$,
  by enumerating the words.
- *The non-reversible cycle after Theorem 6.9.* $\omega_\beta=5.1820$ and $\gamma_\beta=3.4179$,
  computed by hand from the definitions in Section 6.1.
- *Pair face.* Proposition 6.3 (the contour evaluation and the Amos bound) holds, and so does the
  Bessel expansion $(4\pi)^{-1/2}(\omega S)^{1/4}x^{-3/4}e^{\zeta-\gamma x}$.
- *Proofs checked line by line.*
  - The prefactor matching in Proposition 6.5 (powers $\epsilon^{1/4}\cdot\epsilon^{-1}$) and
    formula (layer-c1).
  - Lemmas A.1–A.4, Lemma 5.5, Theorem 4.2(ii), Lemmas B.1 and B.3 and the complex Gaussian
    identity.
  - Lemma 6.8 and Theorem 6.6, including the branch and holomorphy of $\det\mathcal J^{-1/2}$ and
    the choice of $\varepsilon$ with $m^3B_\Psi\varepsilon\le\frac34\sigma_0$.
  - The proof of Theorem 6.9, including the "few visits" and "many visits" estimates.
  - Theorems 7.4 and 7.5, including the refresh form, the Laguerre identity, strict log-concavity
    and the coefficient $W_n(k)=k!(k-1)(N-k)/2$.
  - Corollary 7.6.
  - Lemmas 8.1, D.1 and D.2 and Theorem 8.2, including every numerical inequality in the proof of
    Theorem 8.2.
- *Crossing gaps on the 4-cycle at $N=10^{14}$.* Explicit against implicit forms: 0.035 for the
  vertex–pair crossing and 0.087 for the pair–cycle crossing. The paper's 0.06 is the vertex–3-arc
  crossing (minor point 3).

**Scripts.** `py -I verify_all.py --quick` in `paperC`: **7 of 7 scripts passed in 508 s**.

| Script | Result | Time |
|---|---|---|
| `verify_first_order.py` | PASS | 13 s |
| `verify_second_order.py` | PASS | 45 s |
| `verify_forest.py` | PASS | 306 s |
| `verify_rate_flows.py` | PASS | 2 s |
| `verify_examples.py` | PASS | 11 s |
| `verify_layer.py` | PASS | 79 s |
| `verify_layer_general.py` | PASS | 52 s |

The run rewrote the seven `data/verify_*_output.txt` files with new date headers, as the script
always does. No script was changed, so their sha256 hashes did not change. These files were
already modified in the working tree before the run.
