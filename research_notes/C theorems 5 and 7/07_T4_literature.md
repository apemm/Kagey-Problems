# Principal-minor fibers: exact hypotheses of the sources (checked 2026-10-24)

Sources opened in full: Al Ahmadieh arXiv:2309.00806v2 (full text), Chatterjee–Ghosh–Gurjar–Raj arXiv:2410.01961v1 (full text), Engel–Schneider 1980 (full scanned PDF from Schneider's archive, people.math.wisc.edu/hans/paper_archive/scanned_papers/hs062.pdf).
Only the publisher abstract page was available: Loewy 1986 (ScienceDirect, open archive), Hartfiel–Loewy 1984, Griffin–Tsatsomeros 2006.

## 0. Citation correction (important)

The Loewy paper is **not** in Linear and Multilinear Algebra 19 (1986) 329–337. The correct reference is
R. Loewy, "Principal minors and diagonal similarity of matrices", *Linear Algebra Appl.* **78** (1986) 23–64, doi:10.1016/0024-3795(86)90015-7. I confirmed this on the ScienceDirect page, in Crossref, and in the reference lists of both arXiv papers. I found no Loewy paper on this subject in LMA.

## 1. Loewy 1986 (LAA 78, 23–64)

Verified from the publisher's abstract, which states the theorem in full:
> "Let A, B be n × n matrices with entries in a field F. ... Suppose n⩾4, A is irreducible, and for every partition of {1,2,…,n} into subsets α, β with |α|⩾2, |β|⩾2 either rank A[α|β]⩾2 or rank A[β|α]⩾2. If A and B have equal corresponding principal minors, of all orders, then B or B^t is diagonally similar to A."

- Theorem number: Theorem 1. Al Ahmadieh cites it as [15, Theorem 1], and so does CGGR (Lemma 2.8).
- Field: arbitrary. No restriction on the characteristic is stated.
- Zero entries: allowed. There is no genericity hypothesis and no hypothesis that the minors are nonzero. Only A is assumed irreducible. B is arbitrary, with no irreducibility assumed.
- Irreducibility: A is not permutation-similar to a block upper triangular matrix. Equivalently, the digraph on [n] with arc i→j whenever a_ij ≠ 0 (i ≠ j) is strongly connected. All the secondary sources use this definition. Boussaïri–Chergui phrase it as: A[X,V∖X] and A[V∖X,X] are both nonzero for every proper nonempty X.
- Cut / rank condition: "no cut". A cut is a partition into α, β with |α|, |β| ≥ 2 such that **both** off-diagonal blocks have rank ≤ 1. For irreducible A, rank ≤ 1 means rank exactly 1. Your statement (a) is correct.
- Conclusion: B is diagonally similar to A or to A^T, with D invertible diagonal over F.
- n = 2, 3: Hartfiel–Loewy 1984, Theorem 3 (as cited by CGGR, Lemma 2.8(1)). For irreducible A, PME implies diagonal equivalence. For these n no cut can exist.
- Hartfiel–Loewy 1984 (abstract only): field F; "property D" means B or B^t is diagonally similar to A; their conditions are "in terms of ranks of certain submatrices of A and the concept of irreducibility". Al Ahmadieh reports the HL84 condition as: both A[X,X^c] and A[X^c,X] have rank ≥ 2 for every 2 ≤ |X| ≤ n−2. Loewy weakened this to "at least one of the two has rank ≥ 2". HL84 Theorem 1 is used by both arXiv papers: for irreducible A, every entry of adj(diag(x)+A) is a nonzero polynomial. **I could not open the full texts of HL84 or Loewy86.** I verified only the abstracts and the three consistent secondary statements (Al Ahmadieh, CGGR, Boussaïri–Chergui LAA 485 (2015), Theorem 3 there).

## 2. Al Ahmadieh, arXiv:2309.00806 (v2, 8 Sep 2023)

There is no journal reference on arXiv, and I found no journal version. The bibliography gives Loewy correctly as LAA 78:23–64.

- Field: "over a general field F" throughout. There is no characteristic hypothesis, except in Section 7, which works over C.
- Definitions (Section 2):
  - "Diagonally equivalent": A = DBD^{-1} **or** A = DB^TD^{-1}, with D invertible diagonal. Transposition is included.
  - D(n) is the set of A whose fiber consists of matrices diagonally equivalent to A.
  - Cut: X ⊂ [n] with 2 ≤ |X| ≤ n−2 and rk A[X,X^c] ≤ 1 and rk A[X^c,X] ≤ 1.
  - Irreducible: not permutation-similar to block upper triangular form. Equivalently, the graph G(A) (arc i→j iff a_ij ≠ 0, diagonal ignored) has one strongly connected component (Remark 5.3).
- **Theorem 4.1** (exact): "Let A be an n × n matrix with entries in a field F with n ≥ 4. The matrix A belongs to the set D(n) if and only if A is irreducible and either (a) A is diagonally equivalent to a symmetric matrix or (b) A does not have any cut, that is rk(A[X,X^c]) ≥ 2 or rk(A[X^c,X]) ≥ 2 for all X ⊂ [n], with 2 ≤ |X| ≤ n−2."
  - So yes: the fiber is a single point up to diagonal equivalence iff A is irreducible and (no cut, or diagonally equivalent to a symmetric matrix).
  - The (⇐) direction is Loewy's Theorem 1 plus Lemma 6.1.
- Zero entries and zero principal minors are allowed. No genericity or nonvanishing hypothesis is used. The algebra works with the adjugate G = adj(diag(x)+A) over F[x], whose entries are nonzero polynomials when A is irreducible (Lemma 4.2 = HL84 Theorem 1).
- **Lemma 4.5** (exact setup): A is n×n irreducible over F, n ≥ 4, with cut X = [k]. Write G = adj(diag(x)+A) = [[P, R],[T, Q]], where
  - R_ij = (−1)^i a_i b_j with a_i ∈ F[x_X] and b_j ∈ F[x_{X^c}];
  - T_ij = (−1)^j c_i d_j with c_i ∈ F[x_{X^c}] and d_j ∈ F[x_X].
  
  Then H = [[P, U],[V, Q^T]], with U_ij = (−1)^i a_i c_j and V_ij = (−1)^j b_i d_j, equals adj(diag(x)+B) for some B with det(diag(x)+A) = det(diag(x)+B). The lemma is stated at the level of adjugates. CGGR named the induced operation on A "cut-transpose".
- Lemma 4.3 gives the factorization of the cross entries G_ij (i ∈ X, j ∈ X^c), for irreducible A with a cut.
- Corollary 5.6 and Lemma 5.1:
  - A is irreducible iff f_A = det(diag(x)+A) is an irreducible polynomial.
  - Hence **every matrix in the fiber of an irreducible matrix is irreducible** (Cor. 5.6, stated for n ≥ 4, but the proof does not use n ≥ 4).
- Theorem 6.2 and Lemma 6.1: if A is symmetric and irreducible over F, the fiber is exactly the set of matrices diagonally equivalent to A. The text says this recovers Engel–Schneider Theorem 3.5. Within symmetric matrices the fiber is DAD^{-1} with D = diag(±1).
- Caveats I noticed:
  1. The proof of Lemma 4.4 builds D with entries √α_jk, which need not lie in F (for example over R with α < 0). So the step "A is diagonally similar to a symmetric matrix" in the (⇒) direction may only hold over the quadratic closure. This does not affect the (⇐) direction we would cite.
  2. The text of Example 4.6 says "transpose the submatrix A[X,X]", and in that example it is the X block that ends up transposed. Lemma 4.5 instead transposes the X^c block (Q^T). These differ only by an overall transpose. In CGGR's notation, ct(A,X)^T is a cut-transpose of A^T along X^c, so either convention gives the same class modulo diagonal equivalence.
  3. The second half of the proof is also headed "(⇐)" but proves (⇒). This is only a typo.

## 3. Chatterjee, Ghosh, Gurjar, Raj, arXiv:2410.01961 (v1, 2 Oct 2024)

There is only one version, with no journal reference on arXiv. There is also an ECCC report, TR24-150. **It has not been refereed as far as I can tell.**

- **Theorem 1.1** (exact): "Let A and B be two n × n irreducible matrices over any field. Then, A and B are principal minor equivalent if and only if there exists a sequence of n × n matrices (A = A_0, A_1, …, A_k) with k < 2n such that for 0 ≤ i ≤ k−1, A_{i+1} = ct(A_i, X_i) for some cut X_i of A_i, and A_k is diagonally equivalent to B."
  - Both matrices are assumed irreducible. Since PME preserves irreducibility, this costs nothing.
  - The bound is **k < 2n moves**. The intro says the sequence "contains at most 2n matrices", which is consistent. Section 3 says "cut sequence X of size at most 2n", which is slightly looser and an internal inconsistency. Cite k < 2n.
  - The cut X_i is a cut of the current matrix A_i, not of A.
- Definition 2.5 (cut): n ≥ 4, X ⊂ [n], 2 ≤ |X| ≤ n−2, rank A[X,X̄] ≤ 1 and rank A[X̄,X] ≤ 1. For irreducible A both ranks equal 1. Note that X̄ is also a cut.
- Definition 2.2 (irreducible): not permutation-similar to block upper triangular form. Equivalently, the digraph of nonzero off-diagonal entries is strongly connected.
- Diagonal equivalence: DS to B or to B^T.
- **Definition 2.10 (cut-transpose).** A is irreducible and X is a cut. Write A = [[A[X], p q^T],[u v^T, A[X̄]]], where:
  - q ∈ F^{|X̄|} is the **first nonzero row** of A[X,X̄] and p ∈ F^{|X|} satisfies A[X,X̄] = p q^T;
  - u ∈ F^{|X̄|} is the **first nonzero column** of A[X̄,X] and v ∈ F^{|X|} satisfies A[X̄,X] = u v^T.
  
  Then

      ct(A,X) = [[A[X], p u^T],[q v^T, A[X̄]^T]].

  The X-block is kept, the X̄-block is transposed, and the off-diagonal factors are re-paired: p with u, q with v. Remark 2.11: another rank-one factorization (αp, q/α), (βu, v/β) changes the result by the diagonal similarity diag(αβ I_X, I_X̄). With the canonical choice, ct(ct(A,X),X) = A.
- Lemma 2.12: A and ct(A,X) are PME, for irreducible A over any field.
- Lemma 2.13: for irreducible A, a cut of A is a cut of A^adj, and ct(A,X)^adj is DS to ct(A^adj,X).
- Lemma 2.6: A and (A+D)^adj have the same cuts.
- Zero entries: allowed. The proof first reduces to matrices with all off-diagonal entries nonzero by passing to (A+D)^adj (Section 3 opening, Claim 4.1, Lemmas 2.1, 2.9, 2.15). The core lemmas (3.1–3.9) assume nonzero off-diagonal entries, but Theorem 1.1 itself has no such hypothesis. There is no hypothesis that principal submatrices are nonsingular; the D in the reduction is chosen so that A+D and B+D are invertible.
- Field caveat: Claim 4.1 needs |F| > 10n^5. Otherwise (Remark 4.2) they pass to an extension K. For a finite field, the D in the reduction lives in K. For F = R this is irrelevant.
- Irreducibility of ct(A,X): the paper does not state it as a separate lemma. It follows from Lemma 2.12 together with Al Ahmadieh Lemma 5.1 / Cor. 5.6, and is proved directly in (i) below.

## 4. Engel–Schneider, LAA 29 (1980) 131–138 (full text read)

- Setting: an arbitrary field F, with no characteristic hypothesis and no restriction on n.
  - G(A) = {(i,j) : a_ij ≠ 0}, diagonal included.
  - "Completely reducible" (Def. 2.3(iii)): every arc of G(A) lies on a circuit. By Remark 2.4(ii), this is equivalent to A being permutation-similar to a direct sum of irreducible matrices. Every irreducible matrix is completely reducible.
- **Theorem 3.5** (exact): "Let A ∈ F^{nn}, B ∈ F^{nn}, where A is completely reducible and B is symmetric. Then the following are equivalent: (i) det A[γ̄] = det B[γ̄] if γ is a 1- or 2-circuit of G(B) or γ is a chordless circuit of G(A). (ii) The matrices A and B are diagonally similar."
  - The conclusion is diagonal similarity XAX^{-1} = B with X nonsingular diagonal over F. No transpose is needed, since B^T = B.
  - Equality of all principal minors is more than enough.
  - Zero entries are allowed. Lemma 3.3 shows G(A) = G(B), so A must be combinatorially symmetric.
- The proof works through cycle products: equal circuit products ⇔ diagonal similarity for completely reducible matrices (Bassett–Maybee–Quirk; Fiedler–Pták; Saunders–Schneider (5.1)).
- **Corollary 3.6 (the ±1 ambiguity):** over a totally ordered field, if A and B are symmetric with nonnegative entries and satisfy (i), then A = B. The proof notes that for symmetric A and B, XAX^{-1} = B forces x_i² = x_j² on arcs, so b_ij = ±a_ij. Two symmetric matrices with equal principal minors therefore differ by a signature similarity diag(±1) on each component.
- **Example 3.7(ii), directly relevant to us:** Symmetric cannot be weakened to combinatorially symmetric. The two 4×4 **nonsingular M-matrices** below have full pattern and equal principal minors of all orders, but A is diagonally similar neither to B nor to B^T (Π_(1,3,2,4)(A) = 2, Π(B) = 3, Π(B^T) = 8):

  A = [[10,−1,−2,−1],[−1,10,−1,−1],[−3,−1,10,−1],[−1,−4,−1,10]]

  B = [[10,−1,−3,−1],[−1,10,−1,−1],[−2,−1,10,−1],[−1,−4,−1,10]]

  So nontrivial PME fibers exist inside M-matrices. The intro also mentions Engel–Schneider 1976 (LMA 4:155–176, Cor. 6.7): for completely reducible complex A that is PME to an M-matrix B, A is diagonally similar to an M-matrix.

## 5. Griffin–Tsatsomeros, LAA 419 (2006) 125–171; Holtz–Sturmfels; Oeding

- Griffin–Tsatsomeros Part II (abstract only, ScienceDirect open archive): the paper is about **constructing** some matrix with prescribed principal minors (PMAP), "A condition that implies a constructive algorithm ... will always succeed is presented", plus results on overdeterminacy. From the abstract, it gives no characterization of the full fiber. I could not check the body text, including the exact nondegeneracy condition.
- Holtz–Sturmfels (J. Algebra 316 (2007) 634–648) and Oeding (Algebra Number Theory 5 (2011) 75–109) study the **image** of the principal minor map on symmetric matrices (hyperdeterminantal relations; Oeding proved the set-theoretic Holtz–Sturmfels conjecture). This is per Al Ahmadieh's intro; I did not open these papers. They do not address uniqueness in the fiber for non-symmetric matrices, so they do not bear on our question.

---

## (i) Is a cut-transpose of an irreducible singular M-matrix again an irreducible Z-matrix?

**Answer: yes, if the rank-one factors are chosen correctly. CGGR's canonical choice is a correct one. With an arbitrary choice, the result is a Z-matrix up to the signature similarity diag(−I_X, I_X̄). Irreducibility is always preserved. The concern that the support change could break strong connectivity does not arise.**

Let A be an irreducible Z-matrix with a cut X, and Y = X̄. Write A[X,Y] = −a b^T and A[Y,X] = −c d^T with a, b, c, d ≥ 0. This is possible because a rank-one matrix with all entries ≤ 0 has factors of constant sign on their supports, and irreducibility makes a, b, c, d all nonzero.

*Sign.* In CGGR's normalization:
- q is a row of A[X,Y], so q ≤ 0, and then p ≥ 0;
- u is a column of A[Y,X], so u ≤ 0, and then v ≥ 0.

Hence p u^T ≤ 0 and q v^T ≤ 0. The diagonal is unchanged, A[X] is unchanged, and A[Y]^T is again Z. So ct(A,X) is a Z-matrix. Up to positive diagonal similarity it equals

    ct_Z(A,X) = [[A[X], −a c^T], [−b d^T, A[Y]^T]].

If the factors are rescaled with αβ < 0, the off-diagonal blocks become ≥ 0. The two versions differ by diag(−I_X, I_Y). (A small numerical check, 71 random sparse 6-state generators with |X| = 3: PME held, the result was a Z-matrix, and it was strongly connected in every case.)

*Irreducibility, by algebra.* ct(A,X) is PME to A, so det(diag(x)+ct(A,X)) = f_A, which is an irreducible polynomial. By Al Ahmadieh Lemma 5.1, ct(A,X) is irreducible.

*Irreducibility, by combinatorics.* This also characterizes the new pattern. In G(A), let:
- P = supp a, the X-vertices with an arc into Y;
- Q = supp b, the Y-vertices receiving such an arc;
- U = supp c, the Y-vertices with an arc into X;
- V = supp d, the X-vertices receiving such an arc.

Because A is strongly connected:
- every x ∈ X reaches some vertex of P inside G(A[X]) (take the prefix of a path to Y before its first exit);
- every x ∈ X is reached from some vertex of V inside G(A[X]);
- every y ∈ Y reaches U inside G(A[Y]);
- every y ∈ Y is reached from Q inside G(A[Y]).

The new graph has:
- G(A[X]) unchanged;
- G(A[Y]) reversed;
- the complete bipartite arc sets P → U and Q → V.

In the reversed Y-graph, every y is reached from some vertex of U and reaches some vertex of Q. Now:
- for x ∈ X: x → P → (all of U) → (every y ∈ Y);
- for y ∈ Y: y → Q → (all of V) → (every x' ∈ X).

So the new pattern is **always** strongly connected. The complete bipartite structure of the re-paired rank-one blocks is what makes this work.

*M-matrix property.* B = ct_Z(A,X) is a Z-matrix with the same characteristic polynomial as A, because the characteristic polynomial is det(tI − A) = Σ_k (−1)^k t^{n−k} Σ_{|S|=k} det A[S]. Write B = sI − N with N ≥ 0 and s ≥ max_i b_ii. N is irreducible, and its Perron root is s − (the real eigenvalue of B with smallest real part). The spectrum of B equals that of A, whose smallest real part is 0, attained at the simple eigenvalue 0. So ρ(N) = s and B is an irreducible singular M-matrix. Its proper principal minors are those of A, hence positive. Row sums are generally not zero, because the off-diagonal blocks changed and the diagonal did not. To get a generator, apply the normalization in (iii).

*Consequence for generators.* Combine CGGR Theorem 1.1 with the canonical (Z-preserving) choice at every step. Every intermediate A_i is PME to −Q, so it is irreducible and, by the above, an irreducible singular M-matrix. Therefore:

> Every irreducible generator Q' with the same principal minors as Q is obtained by: applying fewer than 2d canonical cut-transposes to −Q, optionally transposing, and then applying the unique positive diagonal normalization of (iii).

The final diagonal equivalence can be taken with positive D, by the sign lemma in (iii).

## (ii) Reversible Q is determined by its principal minors among all generators

Assume Q is irreducible and reversible with π > 0 (irreducibility gives π > 0).

1. Let S = Π^{1/2}(−Q)Π^{−1/2}. Then S_ij = −√(π_i/π_j) q_ij, and reversibility π_i q_ij = π_j q_ji gives S_ij = S_ji. So S is real symmetric, irreducible, and has the same principal minors as −Q.
2. Let Q' be any irreducible generator with the same principal minors. Then −Q' is irreducible, hence completely reducible. By **Engel–Schneider Theorem 3.5** (F = R, any d, no transpose needed), −Q' = X S X^{-1} for some real nonsingular diagonal X. Hence −Q' = D(−Q)D^{-1} with D = XΠ^{1/2} real diagonal. (For d ≥ 4, Al Ahmadieh Lemma 6.1 gives the same conclusion.)
3. Sign lemma: if C is irreducible and Metzler and DCD^{-1} is Metzler, then all d_i have the same sign. Otherwise strong connectivity gives an arc i→j with d_i d_j < 0, and then (DCD^{-1})_ij = d_i c_ij / d_j < 0. So we may take D > 0.
4. By (iii), a positive diagonal similarity class of an irreducible Metzler matrix contains exactly one generator. So Q' = Q.
5. Reducible generators Q' cannot be in the fiber either: f_{−Q} is irreducible, while a reducible Q' would make f factor (Al Ahmadieh Thm 5.2). So Q is unique among **all** generators with these principal minors.

What needs checking or stating in the paper:
- π > 0;
- Engel–Schneider gives similarity, not just equivalence, because S is symmetric;
- D is real (ES works over the given field R);
- the sign lemma;
- the uniqueness of the normalization.

Extra remark, not needed for (ii): if Q is irreducible and −Q has no cut (d ≥ 4), Loewy's theorem gives −Q' DS −Q or −Q^T. Normalizing −Q^T gives the time reversal Q̂ = Π^{-1}Q^TΠ. So the generator fiber is exactly {Q, Q̂}, which is a single point iff Q is reversible.

## (iii) Spectrum, spectral abscissa, and the unique normalization

- Same spectrum: det(tI − A) = Σ_{k=0}^{d} (−1)^k t^{d−k} E_k(A), where E_k(A) = Σ_{|S|=k} det A[S]. So PME matrices have identical characteristic polynomials and hence identical spectra with algebraic multiplicities. For generators Q and Q', the spectra of Q and Q' coincide, so both have spectral abscissa 0. For irreducible Q, 0 is a simple eigenvalue and every other eigenvalue has negative real part.
- Normalization: let C be an irreducible Metzler matrix that is PME to −Q, i.e. C = −B with B in the fiber. Its spectrum is that of Q, so its spectral abscissa is s(C) = 0.
  - Perron–Frobenius for irreducible Metzler matrices (apply PF to C + sI ≥ 0, irreducible) says s(C) is a simple real eigenvalue with an eigenvector x > 0, unique up to scaling.
  - Existence: put D = diag(x). Then (D^{-1}CD)1 = D^{-1}Cx = 0, and the off-diagonal entries c_ij x_j / x_i stay ≥ 0. So D^{-1}CD is an irreducible generator.
  - Uniqueness: if D' > 0 is diagonal and D'^{-1}CD' has zero row sums, then C(D'1) = 0 with D'1 > 0, so D'1 = λx and D' = λD. A scalar factor cancels in D^{-1}CD.
  - Combined with the sign lemma in (ii), **exactly one** diagonal similarity (up to scalar, real or with signs) turns C into a generator.
  - Note that this uses s(C) = 0, which is supplied by the equal spectra. If s(C) ≠ 0, no diagonal similarity could make C a generator, because generators have 0 in the spectrum.

---

## Confirmed bibliography

- R. Loewy, Principal minors and diagonal similarity of matrices, *Linear Algebra Appl.* 78 (1986) 23–64. doi:10.1016/0024-3795(86)90015-7. (Abstract and theorem verified on ScienceDirect; full text not read.)
- D. J. Hartfiel and R. Loewy, On matrices having equal corresponding principal minors, *Linear Algebra Appl.* 58 (1984) 147–167. doi:10.1016/0024-3795(84)90209-X. (Abstract only. The publisher metadata misspells the author as "Leowy".)
- G. M. Engel and H. Schneider, Matrices diagonally similar to a symmetric matrix, *Linear Algebra Appl.* 29 (1980) 131–138. doi:10.1016/0024-3795(80)90234-7. (Full text read.)
- A. Al Ahmadieh, The fiber of the principal minor map, arXiv:2309.00806 [math.AG], v2, 8 Sep 2023. (Full text read; no journal version found.)
- A. Chatterjee, S. Ghosh, R. Gurjar, R. Raj, Characterizing and testing principal minor equivalence of matrices, arXiv:2410.01961 [cs.CC], v1, 2 Oct 2024; also ECCC TR24-150. (Full text read; no journal version found.)
- K. Griffin and M. J. Tsatsomeros, Principal minors, Part II: The principal minor assignment problem, *Linear Algebra Appl.* 419(1) (2006) 125–171. doi:10.1016/j.laa.2006.04.009. (Abstract only.)
- A. Boussaïri and B. Chergui, Skew-symmetric matrices and their principal minors, *Linear Algebra Appl.* 485 (2015) 47–57 (arXiv:1403.0095). (Used only as a secondary statement of Loewy's theorem.)
- Not opened (cited via Al Ahmadieh): O. Holtz and B. Sturmfels, *J. Algebra* 316(2) (2007) 634–648; L. Oeding, *Algebra Number Theory* 5(1) (2011) 75–109.
