Independent referee report received October 24, 2026 (twelve readers over both papers, seven on C and five on F). Kept here as the basis of the revision.

# Summary

Paper F, "lattice Lévy walk" (`paperF/problem131_levy.tex`, commit 0ffc041, sha256 `2a55b92f…cfe0d7`, 53 pp in the EJP class), describes the law $P_N$ of the number of right steps after $N$ steps of an alternating renewal walk whose run lengths have regularly varying tails of index in $(1,2)$. The results are a bulk local limit theorem uniform over the whole row (Theorem A), a big-jump kernel $G_N$ with the exact coefficient $\gamma$ on the zone $k-pN\ge K\lambda_NB_N$ together with the boundary layer and the endpoint atoms (Theorem B), the effect of an arbitrary preparation with sharp criteria (Theorem C), the global mode and the golden-ratio threshold (Theorem D), a second-order coefficient and the antimode $T_\mp(j^*)\sim2\alpha_\pm s/N$ (Theorem E), and identification of both run laws from the ends (Theorem F). The proofs combine first-run and last-run decompositions with renewal kernels, Fuk–Nagaev and local large-deviation bounds, and Frenk's second-order renewal theorem.

Coverage was complete for all five lanes. Four independent readers covered correctness and adversarial checks on Sections 2–3, 4, 5, and 6–8 (the last including the verification section); a fifth covered claims, notation and exposition over the whole paper. All displayed constants that carry a conclusion were recomputed, including $C(\varphi)=0.7761317$, the 0.9513 bound, $C(j)$ and the antimode coefficient. Not checked: external sources (Berger's Theorem 3.3 and PTRF Theorem 2.4, Frenk 1982, wsdb2018, akimoto2023), the Lean library and the figure images.

No critical or major mathematical defect was found. The concerns below are statement and framing problems with local fixes.

# Main mathematical concerns

None at critical or major level.

# Other mathematical concerns

1. **The conjecture for the partial window double counts the big jump** (moderate, confidence 0.85; `sec_bigjump.tex:103-104`). The paper conjectures $P_N(k)=(1+o(1))(B_N^{-1}h_N(x_{N,k})+G_N(k))$ on $KB_N\le k-pN\le K\lambda_NB_N$. At the top of that window Theorem B(b) gives $P_N\sim G_N$, and by Remark `rem:no-single-formula` the ratio $h_N(K)/(B_NG_N(k))$ tends to one as $K\to\infty$, so the conjectured sum is about $2G_N$ there. Replace it with an expression that reduces to each side at the two ends of the window, or drop it.
2. **Censored-run attribution** (minor, 0.8; `sec_bigjump.tex:689-691`, `sec_intro.tex:177-178`). In $I_+=\mu_-^{-1}[\alpha(1-\ell)\ell^{-\alpha-1}+\ell^{-\alpha}]$ the censored run contributes the $+\ell^{-\alpha}$ term, which changes the exponent from $-\alpha$ to $-(\alpha-1)$. The sentence crediting the whole linear term to the censored run should say this.
3. **Theorem F(b) has a redundant hypothesis** (minor, 0.9). Under (RV), $Q_+(N)/T_+(N)\to q$ already gives $\nu_+(n)=o(T_+(n))$.
4. **Theorem C(d), converse** (minor, 0.8; `sec_preparation.tex:347-351`). It uses $T_-(j)>0$, which (RV) for the plus sign does not supply. Add the hypothesis or the case split.
5. **Justification of `eq:lambda-unif`** (minor, 0.85; `sec_preparation.tex:128-136`). $\lambda_n=\lambda_N+o(1)$ on $[cN,N]$ is false when the indices differ; the bound actually used holds, so only the sentence needs replacing.
6. Local slips (all minor): $q_m$ written as a full convolution although $T_\sigma=1$ at nonpositive arguments (`sec_setting.tex:248`); the fixed-$K$ assertions in `rem:no-single-formula` fail at the equality case $K^*\approx1.85$ and when $\theta_{-,N}$ oscillates; the opening of Section 4 says bins outside the bulk are smaller "by a power of $N$", which fails near $KB_N$.

# Exposition and organization

- **The new part of Theorem A is buried** (moderate). Related work says Berger's Theorem 3.3 with the fresh-plus identity already gives the window $|k-pN|\le KB_N$, and that the new content is the uniform bound $C/B_N$ over the whole row and the control of remote bins under (RV) alone. Sections 2–3 spend their length on machinery an expert will recognise and do not foreground that content. Move the routine kernel identities to an appendix and open Section 3 with the uniform statement and the reason it needs new work.
- **Theorem C(c) packs four claims** with different hypotheses and an implicit target into one item. Split it into a statement for the full zone and a separate statement for the interior zones with the window condition $W_n$.
- **Numbered constants are reassigned** across sections, against the convention the paper states. Number constants per proof or rename the reused ones.
- The abstract runs to 323 words and reads as a table of contents. A version near 200 words that names Theorems A, B and the sharpness of (LR) would serve an editor better.

# Claim and scope assessment

- **Location of the partial window** (moderate, 0.8). The abstract says one window is described only in part "when the runs of right steps have the smaller fluctuation scale". The model is symmetric, so the window lies on the side of whichever sign has the smaller scale. As written, the abstract implies that no window exists when the minus runs are the smaller ones. State it by side.
- **"Invisible in the bulk"** (moderate, 0.8; `sec_intro.tex:119-120`). Theorem C(b) gives a criterion for the approximation uniformly over $1\le k<N$, and says the interior approximation needs no condition on the preparation. The introduction's phrase "invisible in the bulk exactly when $B_n(\nu_+(n)+\nu_-(n))\to0$" therefore misdescribes the theorem; say "uniformly over the row".
- **Theorem F is stated as more than it is** (minor, 0.8). For a fresh plus start $P_N(N)=T_+(N)$ by Proposition `prop:fresh-identity`, so the plus law is read off the atoms directly. The minus law needs the boundary layer at the plus end, and the thinning remark (why the minus-end normalization cannot be replaced by $\sum_nf_+(n)=1$) is the genuinely informative part. A proposition with that content is more accurate than a lettered theorem.
- **Sharpness of (LR)** (minor, 0.6). The introduction calls it open, while Remark `rem:wr` shows that (RV) alone does not suffice for Theorem B. Align the two, saying exactly what remains open (for example, whether a weaker local condition than (LR) suffices).
- **Positioning of Theorem B against Berger, PTRF, Theorem 2.4** (moderate, conditional, 0.6). The paper cites the local one-big-jump theorem under exactly (LR) and says the proof does not use it. A referee will ask why that theorem, applied to the walk of run lengths, does not give Theorem B. The answer (random number of runs, the censored final run, uniformity to the endpoint) should be stated in two sentences. The external theorem was not re-read here.
- **Missing classical sources** (minor, final-referee observation). Takács (1957, 1959) and Kesten (1962), the classical integral limit theorems for the sojourn time of an alternating renewal process, are not cited, although the authors' own prior-art note recommends it. Borovkov and Mogulskii's local theorems for compound renewal processes assume Cramér's condition, and Starreveld, Bekker and Mandjes (arXiv:1602.05131) treat finite variance and light tails, so neither overlaps.
- Positioning against wsdb2018 and akimoto2023 for the boundary layer and the preparation results is unstated (minor, conditional).

# Questions for the authors

1. Why does Berger's PTRF Theorem 2.4 not give Theorem B directly, and does any part of the proof of Theorem B reduce to it?
2. What is the conjectured form of $P_N$ on the window $KB_N\le k-pN\le K\lambda_NB_N$ that agrees with Theorem B at its top and with the bulk at its bottom?
3. Is any local condition strictly weaker than (LR) known to suffice for Theorem B?

# Suggested revisions

1. Replace or drop the window conjecture.
2. Restate the partial window by side in the abstract and Section 1.
3. Reword the bulk criterion in the introduction to match Theorem C(b).
4. Add the two-sentence comparison with Berger PTRF Theorem 2.4; cite Takács and Kesten.
5. Demote Theorem F to a proposition, or state plainly that the plus law comes from the atoms; drop the redundant hypothesis in (b).
6. Fix the censored-run sentence, the converse in C(d), the `eq:lambda-unif` justification and the local slips in item 6 above.
7. Foreground the new content of Theorem A, split Theorem C(c), renumber constants, and shorten the abstract.

# Overall assessment

The mathematics held up under a line-by-line read with every load-bearing number recomputed. The paper gives a complete description of the law by zones, with exact constants and a sharpness statement for (LR), and a rigorous lattice version of the Lévy-walk infinite density with its boundary layer and atoms, which the physics papers it cites leave without proof. The remaining problems are in how three statements are framed (the window conjecture, the side of the window, the bulk criterion) and in positioning against Berger's local theorems. These are revisions of a few days. This review does not certify novelty beyond the sources named above.
