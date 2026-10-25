Independent referee report received October 24, 2026 (twelve readers over both papers, seven on C and five on F). Kept here as the basis of the revision.

# Summary

Paper C (`paperC/problem131_chains.tex`, commit 0ffc041, sha256 `23a9ae7c…ab56`, 95 pp in the source class) asks which states the most likely occupation-count vector of a finite Markov chain uses after about $\tau\log N$ switches in $N$ steps. The forward theory is a stratified local law in each face of the simplex, a face-selection rule weighing lattice entropy against the killed Donsker–Varadhan functional, crossings located to $o(1)$ with the $\tfrac12\log\log N$ term, the window of tied faces, a facet boundary layer with a Bessel kernel (unconditional for faces with at most three states, under Hypothesis L otherwise), the complete graph and the near-vertex regime. The second half is identifiability: $J_V$ determines exactly the principal minors of $-Q$ (Theorem D), the modal-support map does too (exposure lemma with the Perron-branch lemma), the fiber is finite and equals $\{Q,Q^*\}$ without a cut, a reversible design with $m+d-1$ coordinates, a class-uniform finite-horizon theorem, and at low temperature a cycle hierarchy whose tree is read off by rewards of known size.

Coverage was complete for all five lanes. Six independent readers covered correctness and adversarial checks on Sections 2–4 with the first-order appendix, Section 5 with the torus and Laplace appendices, Sections 6 and 8 with the vertex appendix, Section 7 with its appendix, Section 9, and Section 10. A seventh covered claims, notation and exposition over the whole paper. Numerics confirmed the local law, the transfer, the constants, the 4-cycle crossings, the $d=4$ example, the finite-horizon constants, the four-state low-temperature example and the attraction theorem. Not checked: external sources (Loewy, Hartfiel–Loewy, Al Ahmadieh, Chatterjee–Ghosh–Gurjar–Raj, Kim–Landim, Catoni and Trouvé), the Lean modules and the figures.

No critical or major mathematical defect was found. The finite-horizon theorem and the cycle-tree reconstruction were read in full and found sound apart from two minor slips.

# Main mathematical concerns

None at critical or major level.

# Other mathematical concerns

1. **Controlled boundaries are underspecified** (moderate, 0.7; `sec_reconstruction.tex:108-114`). Definition `def:controlled` asks for the same strict winner "outside a closed nowhere dense set" of $(\tau,v)$ "with $\bar v$ large", without naming the ambient space or saying how large $\bar v$ must be or on what it depends. The exposure induction applies the definition literally, so the steps inherit the ambiguity. State the space (the open quadrant of $(\tau,v)$ with $v\le0$, say) and quantify the threshold before the induction uses it.
2. **Theorem `thm:nonreversible`(d) is stated for every irreducible Z-matrix** (minor, 0.85). The clause "exactly one positive diagonal similarity turns it into a generator" fails for $3I-P$ with $P$ irreducible and stochastic: that matrix is nonsingular, while the negative of a generator always has the eigenvalue $0$, and similarity preserves the spectrum. The clause holds for $C$ in the principal-minor fiber of $-Q$, which is the case used.
3. **Hypothesis L** (question, 0.55). The paper's open-problems paragraph (`sec_boundary.tex:607-612`) already names the missing step: a Laplace lemma for a complex symmetric Hessian with positive definite real part, with constants. The torus representation extends to complex weights by domination, and the holomorphic implicit function theorem gives the complex critical point. Shifting the torus contour through that point and applying the complex-phase Laplace method should give the hypothesis with $|\varepsilon|\le C/S$ uniformly on compacts. One reviewer's numerics for $|G|=3$ agree with the hypothesis to the stated order. This is a suggested route, not a verified proof.
4. Smaller items (all minor): $v=0$ lies in the exceptional set of part (f) for every start, so the statement should exclude it; the survival-probability paragraph (`sec_reconstruction.tex:47-51`) applies the Perron-branch lemma to $Q'$ without saying $Q'$ is irreducible; the identity $w=bu^2=\omega Sh$ (`sec_boundary.tex:602`) holds only up to $p^{-2}$; the heuristic before `thm:simplex-balance` is false for unequal run counts; the remark at `sec_lowtemp.tex:179-180` that lower-order terms always break exact ties fails in the symmetric case the section treats; the uniformization bound in the proof of `lem:killed-depth` is wrong when some $V_{ij}=0$ and $\gamma=0$. None affects a theorem.

# Exposition and organization

- **Two papers in one** (moderate). Sections 9 and 10 use only the first-order results, Proposition `prop:uniform-facemax` and Definition `def:tilt`. The interface between the forward theory and the identifiability theory is that narrow and is never stated. At 95 pages this is the first thing an editor will see.
- **The identifiability induction is hidden** (moderate). Lemma `lem:exposure` says that its ranges depend on the second generator and that it is a statement of identifiability, but the induction over faces that proves `thm:nonreversible`(a) sits inside its proof. Promote it to a proposition: for $Q,Q'$ with different minors there is an open set of $(\tau,v)$ on which the strict winners differ.
- **Notation**: $d,\delta,\tau,D,h$ carry two meanings in single statements of Section 9, and the orientation or normalization of the score, the lines $\ell$, $J$ and $\lambda$ changes between Sections 7 and 9 (complete graph and reconstruction).
- **Citation pointers**: the Kim–Landim numbering note, the list of results quoted from paperA, "incorporates" for paperB and the exponent in Good's formula do not match their use.

# Claim and scope assessment

- **Bessel kernel in the abstract** (moderate, 0.85). The abstract says "Near a facet the law follows a Bessel kernel, which we prove for faces with at most three states". Theorem `thm:layer`(b) gives a log-form bound in general and the relative Bessel form only for reversible $Q$ or $x\le CT^{1/3}$; the non-reversible cycle ratios 19.6, 265 and 48268 show that the restriction is real. The opening of Section 6 also says the constants match the local law, while Proposition `prop:layer-prefactor` assumes reversibility. Qualify both.
- **The observation model** (moderate, 0.65). The introduction notes that the survival probability gives $\lambda_V$ on all fields and so every minor at once. The case for observing only the modal support then rests on one sentence. A referee will ask in what experiment one sees the support of the most likely composition without being able to estimate a probability. Give one concrete setting, or present the modal-support result as a statement about how much the forward theory's output retains.
- **Borrowed and new** (minor, 0.65). The introduction says the principal-minor fiber "is known up to diagonal similarity and transposition", omitting the no-cut condition and the cut-transposes, although the section's own "What is borrowed" paragraph credits Chatterjee, Ghosh, Gurjar and Raj (Theorem 1.1) correctly. Make the introduction match. Whether the irreducibility lemma is already in Al Ahmadieh (2023) was not checked here.
- "Solved exactly" for the complete graph and "read off the cycle tree" compress the statements a little; tie each to the theorem it summarizes.

# Questions for the authors

1. Can Hypothesis L be proved for $|G|\ge3$ by the complex-phase Laplace method sketched above? If not, where does the argument fail?
2. In what setting is the modal support observable while the survival probability is not?
3. Is the irreducibility of $R_F$ over $\mathbb C$ (Lemma `lem:RF-irreducible`) in Al Ahmadieh (2023) or another source?

# Suggested revisions

1. Make `def:controlled` precise and check each step of the exposure induction against it.
2. Restrict `thm:nonreversible`(d) to the fiber of $-Q$; exclude $v=0$ in (f); add irreducibility of $Q'$ in the survival-probability paragraph.
3. Attempt Hypothesis L; if it does not go through, state `thm:layer` unconditionally for faces with at most three states and move the conditional extension to a remark.
4. Qualify the Bessel claim in the abstract and the opening of Section 7.
5. Motivate the observation model or reframe it; fix the borrowed/new sentence in the introduction.
6. Split the paper along the interface in the first exposition item, or at least state that interface in the introduction.
7. Promote the identifiability induction to a proposition; fix the notation and citation pointers and the minor slips.

# Overall assessment

The mathematics is in good condition: seven reviewers found no error that touches a theorem, and the explicit examples and constants reproduce. Theorem D answers the question left open by Kim and Landim's Example 5.4, and the low-temperature cycle reconstruction is a clean result. The weaknesses are size and focus. The paper carries two programs with a narrow interface, one theorem still rests on a hypothesis in its general form, and the second program's observation model needs a stronger case. The review does not certify novelty against sources it did not read.
