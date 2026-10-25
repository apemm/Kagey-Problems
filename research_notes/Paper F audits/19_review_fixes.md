# 19. Review fixes for Paper F (25 October 2026)

Source of the items: the F section of the 25 October review and its raw file for F (issues F001 to F007), and the "do first" list of the F plan. Every item is done in the TeX. The paper now has 63 pages. The build is clean apart from the class's `pagebackref` notice, which was there before. `py -I verify_all.py --quick` passes all 5 scripts.

## Literature check for the window credit

- **Rozovskii 1997.** Theory Probab. Appl. 42 (1997), no. 3, 454–482. The Russian original is Teor. Veroyatnost. i Primenen. 42 (1997), no. 3, 496–530, MR1618791, DOI 10.1137/S0040585X9797626X.
  - The English page numbers and the title ("... from the domain of attraction of an asymmetric stable law") come from the Crossref record. DDS cite the Russian pagination 496–530 under the English journal name. We cite both.
  - What it proves, from the Crossref abstract: an asymptotic representation of the tail of $S_n$, uniform over $x>0$, for the domain of attraction of an asymmetric stable law with index in $(1,2)$.
  - DDS (Section 9.2, before Theorem 9.2) say that the global form of their Theorem 9.2 is Rozovskii's Corollary 2A. That form is $P(S_n>x)\sim nP(\xi>x)$ uniformly for $x\ge t(c\log n)^{(\alpha-1)/\alpha}b_n$, for every $t>1$.
  - DDS's introduction says Rozovskii studies deviations "beyond the big-jump domain".
- **DDS 2008.** Section 9.2 covers a centred step whose left tail is regularly varying with index $-\alpha$, $\alpha\in(1,2)$, and whose right tail is regularly varying with index $-\gamma$, $\gamma>\alpha$. Their Proposition 9.2 and Theorem 9.2 give the local form on the same range. I checked this in the arXiv text (math/0703265v3). The constant inside the logarithm is garbled in the extracted text, so the paper writes "an explicit constant $c$ that depends on the two indices".
- **Converse direction.** Rozovskii's representation is uniform over all $x>0$, so it covers the range below the boundary for the tail of sums. The paper therefore does **not** claim the converse as new. It says that what is new is the count at a fixed time: the number of runs is random, the big jump can be the run in progress, and equal indices with a slowly varying scale ratio are covered.
- **Rozovskii 1993.** "Probabilities of large deviations on the whole axis", Theory Probab. Appl. 38 (1993), no. 1, 53–79. Crossref dates the English issue to 1994. The Russian original is 38 (1993), 79–109, MR1317784, DOI 10.1137/1138005.
  - I found no abstract or full text. Only the title and how DDS and Berger–Birkner–Yuan cite it are known.
  - So the paper cites it only as "see also" at the conjecture remark.
- **Composite form.** For sums, the global composite form (the moderate-deviation term and the big-jump term in one formula, uniform in $x>0$) is in Rozovskii 1997. The remark now says this, and calls the conjecture the local analogue for the count.
- **Limits.** I did not read the full text of either Rozovskii paper, since both are behind a paywall. Two statements rest on the Crossref abstract and on DDS's description:
  - "uniform in $x>0$";
  - "covers the range below the boundary".
  Check these against the original before submission.

## Changes

1. **Window credit.**
   - sec_bigjump.tex, opening of Section "The start of the zone": a new paragraph states the sums result. It gives Rozovskii's Corollary 2A for the tail and DDS's Proposition 9.2 and Theorem 9.2 for local probabilities, notes that the boundary has the same order, and says what is new.
   - sec_intro.tex: the same credit in the Theorem B paragraph.
   - Two new bibliography entries: `rozovskii1993` and `rozovskii1997`.
2. **Abstract hypotheses.** The abstract now reads "For a fresh start, when the ratio of the two run scales tends to infinity ... on the side of the smaller scale". This matches the theorem: $b_-/b_+\to\infty$ gives both $b_+\le b_-$ eventually and $\theta_{+,N}\to0$. The intro now:
   - limits "every theorem below holds for every relation between the two scales" to all theorems except Theorem window;
   - states the general exception as the window $KB_N\le k-pN\le K\lambda_NB_N$;
   - says that Theorem window narrows it for a fresh start with $b_-/b_+\to\infty$.
3. **Wang–Schulz–Deng–Barkai.**
   - Abstract: "For the occupation count of the lattice walk with index between 1 and 2, this answers a question of ...".
   - Intro: their sentence is quoted without the added words "of the occupation time". The intro notes that their question also covers their other observables and $0<\alpha<1$, and that Theorem C answers it for the occupation count with $1<\alpha<2$.
4. **Two false sentences in the intro.**
   - The profile is eventually monotone when $\nu_-(n)=(c+o(1))T_-(n)$ with $c\ne1/\mu_-$, in particular when $\nu_-=o(T_-)$ (Lemma prep-diff). The difference renewal theorem is now stated under (RV) and (SPAN).
   - The bound "one mode more than the two profiles" is now stated under $\nu_\pm=o(T_\pm)$.
   - "A prepared start has at least four modes" now reads "some prepared starts", with the start of Corollary four-modes described.
5. **Other items.**
   - Conjecture three-modes is now the upper bound: at most $M_++M_-+1$ modes for all large $N$. A paragraph after it explains three things:
     - with Theorem modes-lower it gives the exact count;
     - Theorem modes-lower proves the "only if" direction of the three-mode criterion;
     - the upper bound is open.
     The intro sentence matches.
   - Monotonicity of $\mathcal I(m,d)$ in $m$: the justification is now that $\psi^*$ is convex with $\psi^*(0)=0$. So $\psi^*(v)/v$ is nondecreasing, and $\mathcal I=d\,\psi^*(d/m)/(d/m)$.
   - sec_verify.tex: "so at this $j$ it decays like $1/N$". The check is at a single $j$, as the review notes.
   - README.md updated to match: the WSDB scope, the window credit, and the conjecture as an upper bound.
6. **Lean.**
   - The PaperF library is now recorded in `build-log.txt` and `verification-manifest.json`, by commit 0c65143, which is after the review.
   - The sentence in sec_verify.tex is accurate, so it is unchanged. The Section 2 identities are in Lean. The bound in Lemma counting is not, because `Exact.TwoLong` proves it for a weaker event, as MAP.md says.
   - I did not touch `lean/`.

## Not done

- The reviewer's numbers for the law conditioned on runs $\ge2$ (extra modes up to $N\approx3000$) are not in the paper. They come from no script in the repo. The conjecture already says "for all large $N$".
- I did not restate the window theorem along subsequences. Fixing the abstract was enough.
