# Hereditary marked bridges and sharper counting exponents

9 November 2026. A geometric restriction improves the general marked-transfer bound. For every balanced partition at height \(h\ge4\), double insertions cannot return from a later sea component to an earlier one. Consequently, if \(q=\lfloor h^2/4\rfloor\), \(\rho\) is the largest sea-component radius, and \(k\) is the largest number of radius-\(\rho\) sea components on one sea path, then
\[
 b_\pi(m)=O\!\left(m^{q+k-1}\rho^m\right).
\tag{1}
\]
This is unconditional. It does not establish \(k=1\), unique dominance, or positive access to every maximal component.

The previously available general transfer bound was \(O(m^{(q+1)k-1}\rho^m)\). Its abstract reset example remains valid for arbitrary marked matrices. The additional geometric lemma below excludes that reset mechanism for hidden-free blackout words.

## 1. Fixed-pair-set validity

Fix a row-pair set \(F\). Consider a word \(B=(B_x)\) whose columns contain one or two black rows, and assume that every two-row column is an edge of \(F\).

Call the word hidden-free \(F\)-valid when:

* no tilted rectangle is completely black;
* no two tilted rectangles have the same presentation;
* no tilted presentation of size one or two has an axis-aligned rival under the fixed pair set \(F\).

The rival conditions are the paper's local formulas. A singleton \((x,r)\) has a rival when some \(s\in B_x\) satisfies \(\{r,s\}\in F\). A vertical pair has a rival when its row pair belongs to \(F\). A horizontal pair in columns \(x,z\) has a rival when \(B_x\cap B_z\ne\varnothing\). An oblique pair \((x,r),(z,s)\) has a rival when its crossed cells \((x,s),(z,r)\) are black.

These conditions use the final fixed pair set, even if some of its labeled double columns lie outside the local word.

## 2. Deleting black cells preserves hidden-free validity

**Lemma.** Let \(B\) be hidden-free \(F\)-valid. For each column choose a nonempty subset \(B'_x\subseteq B_x\). Then \(B'\) is hidden-free \(F\)-valid with the same pair set \(F\).

**Proof.** A newly hidden tilted rectangle is impossible because its four corners would already have been black in \(B\).

If distinct tilted rectangles \(R,Q\) have the same presentation under \(B'\), then
\[
 C(R)\triangle C(Q)\subseteq B'\subseteq B.
\]
They already have the same presentation under \(B\), contradicting validity. This argument also covers a change in the color of their common corners.

It remains to exclude a newly appearing axis rival.

For a singleton presentation \(\{w\}\), the other three rectangle corners and the black cell witnessing its \(F\)-rival remain black in \(B\). If \(w\) remains white, the same old singleton rival exists. If \(w\) was black, the old rectangle was hidden.

For a vertical presentation \(\{w_1,w_2\}\), its row pair lies in \(F\). If neither point was black in \(B\), the same pair rival existed. If exactly one was black, the other was an old singleton presentation with an \(F\)-rival in its own column. If both were black, the old rectangle was hidden.

For a horizontal presentation
\[
 w_1=(x,r),\qquad w_2=(z,r),
\]
let the retained black cells witnessing the rival be \((x,t),(z,t)\), with \(t\ne r\). If one of \(w_1,w_2\), say \(w_1\), was black in \(B\), its old column contained both \(r,t\), so \(\{r,t\}\in F\). If the other point was white, it was an old singleton presentation with an \(F\)-rival through its retained row-\(t\) cell. If both were black, the old rectangle was hidden. If neither was black, the old horizontal rival existed unchanged.

For an oblique presentation
\[
 w_1=(x,r),\qquad w_2=(z,s),
\]
the crossed cells \((x,s),(z,r)\) are retained black cells. If exactly one displayed point was formerly black, that old column was the double \(\{r,s\}\), which belongs to \(F\). The other point was therefore an old singleton with an \(F\)-rival. The cases of zero or two formerly black points give the old oblique rival or a hidden rectangle.

All possibilities contradict hidden-free \(F\)-validity. \(\square\)

The hypothesis excluding hidden rectangles is necessary. A hidden unit diamond can use the central double \(\{r-1,r+1\}\in F\). Reducing that double to either endpoint exposes the other central point as a singleton with a virtual \(F\)-rival. The pair set remains fixed although that particular double has been deleted.

## 3. Marked paths respect sea reachability

Use the exact history automaton of memory \(L=2W_h\). A recurrent singleton component consists entirely of full-length singleton histories. The transient histories containing doubles are retained when marked transitions are allowed.

**Proposition.** Suppose a hidden-free \(F\)-valid marked path starts at a recurrent pure-sea state \(u\) and ends at a recurrent pure-sea state \(v\). Replace every double letter along that path by either one of its two rows. The resulting singleton word gives a sea path from \(u\) to \(v\).

The starting and ending histories are unchanged: they contain no double letters. Every forbidden configuration in the replacement path would contradict the deletion lemma applied to the same finite window of the original path. If needed, prepend a valid sea past to \(u\), so all initial boundary windows are contained in the word; the memory bound makes the choice of earlier past irrelevant.

Thus, if a marked path goes from sea component \(C\) to sea component \(D\), then \(D\) is reachable from \(C\) using singleton transitions alone. In particular, marked bridges cannot reverse the sea condensation order.

The strengthened [hidden-rectangle theorem](hidden_rectangles_and_exact_hypergraph.md) proves that every identifying blackout on a board with both dimensions at least four is hidden-free. Therefore the proposition applies throughout every accepted equality word at every balanced partition when \(h,m\ge4\). The thin height-three case remains an exception.

## 4. Counting critical components

Let \(\rho\) be the largest sea-component spectral radius. Call a sea component critical if its radius is \(\rho\), and let \(k\) be the largest number of distinct critical components on one directed sea path.

In the exact used-edge automaton, recurrent components are copies of sea components, indexed by the set of already used double labels. An accepting path uses exactly \(q\) marked letters.

List its visited critical recurrent copies in chronological order. By Section 3, the underlying sea components occur in their sea reachability order. They cannot leave a component and later return to it through a different component. Hence there are at most \(k\) distinct underlying critical components.

If two consecutive entries in the list have the same underlying sea component but are different recurrent copies, at least one double label was used between them. Otherwise the used-edge subset is unchanged and they belong to the same recurrent component of the exact automaton. Such repetitions therefore consume distinct marked transitions. There are at most \(q\) of them.

The total number of critical recurrent copies visited is consequently at most
\[
 q+k.
\tag{2}
\]
The usual nonnegative resolvent decomposition now gives (1): each critical component contributes a simple Perron pole, and a path through at most \(q+k\) such components has pole order at most \(q+k\). Periodic components do not change the polynomial upper bound.

This argument does not require the critical sea components to be accessible on an accepted path. Including inaccessible components only weakens the bound.

For comparison, the abstract matrices
\[
 T=\begin{pmatrix}2&1\\0&2\end{pmatrix},
 \qquad
 E=\begin{pmatrix}0&0\\1&0\end{pmatrix}
\]
allow a marked transition from the second sea component back to the first. They give the larger degree three with \(q=1,k=2\). Such a reset contradicts Section 3 and therefore cannot model a hidden-free fixed-\(F\) blackout bridge. The earlier abstract counterexample disproves the inference from arbitrary marked matrices; it does not disprove the new geometric statement.

## 5. Why no hidden correction remains at height at least four

The earlier classification left a possible unit diamond. The strengthened theorem eliminates it when both board dimensions are at least four. A unit diamond can be translated by one of its diagonal side vectors toward the available horizontal and vertical margins. The translated diamond and the rectangle doubled in that direction have symmetric difference equal to the original diamond. Thus its four black corners already force a collision.

Accordingly, the exact local automaton may reject every hidden rectangle outright for all sufficiently long words at fixed height \(h\ge4\). The proof of Sections 3–4 applies to each partition without a hidden marker or a reset exception. Writing the partition dependence explicitly gives

\[
 b_\pi(m)
 =O\!\left(m^{q+k_\pi-1}\rho_\pi^m\right),
 \qquad k_\pi\ge1.
\tag{3}
\]
For \(k_\pi=1\), this gives the degree upper bound \(q\).

The same restriction can be applied to any chosen exponential radius after trimming to the relevant accepting paths. It is not a proof that the leading degree equals the upper bound; accessibility and positive insertion weights still determine which critical chains occur.

## 6. What this resolves

The deletion lemma and the strengthened no-hidden theorem supply the missing structural input for the sharper exponent \(q+k-1\) at every balanced partition when \(h\ge4\). A marked insertion cannot make a sea component accessible in a direction that singleton transitions prohibit.

It does not prove that every recurrent component reaches the canonical component, or that the canonical component has the largest Perron root. A component disconnected from the canonical component under sea transitions remains disconnected in the same direction under hidden-free marked bridges. General dominance and balanced-partition comparison therefore remain separate questions.

## 7. An unconditional product formula for collared words

The same lemma gives an exact asymptotic for a natural subclass, without assuming global sea dominance.

Fix a balanced partition \(\pi\), and let \(C_\pi^\partial\) be the primitive sea component containing the constant row-1 and row-\(h\) states. The boundary-switch and isolated-insertion theorem establishes this component for every partition. For parity it is the canonical component \(C_*\), which also contains every other constant state.

Let \(d_\pi(m)\) count the equality words of length \(m\) with each edge of \(E_\pi\) used once and with the first and last \(L\) columns all equal to the singleton row 1. For fixed \(h\ge4,\pi\),
\[
 d_\pi(m)\sim
 C_\pi^\partial\,m^q(\lambda_\pi^\partial)^m,
 \qquad C_\pi^\partial>0,
\tag{4}
\]
where \(\lambda_\pi^\partial\) is the Perron root of the boundary component. The hidden-free property is automatic by Section 5, so (4) counts every equality word with these fixed collars, for every balanced partition.

To prove this, take any pure-sea state encountered on a marked path from \(1^L\) back to \(1^L\). Deleting the doubles separately on the prefix and suffix gives singleton paths in both directions. The state therefore lies in \(C_\pi^\partial\).

In the local history matrices, delete every full-length pure-sea history outside \(C_\pi^\partial\), and retain all admissible histories containing a double. Denote the resulting singleton and double matrices by \(\widetilde T,\widetilde E_e\), with every hidden transition rejected. No counted collared word is lost. Conversely every remaining accepted marked loop is one of the collared words, so this is an exact restriction.

The only recurrent component of \(\widetilde T\) is \(C_\pi^\partial\). A history containing a double is flushed after at most \(L\) singleton steps. Thus \(\lambda=\lambda_\pi^\partial\) is the unique dominant eigenvalue of \(\widetilde T\), it is simple, and every other eigenvalue has strictly smaller modulus. Let \(v,u\) be nonnegative right and left Perron vectors, and put
\[
 \Pi=\frac{vu}{uv},\qquad
 B=\alpha\Pi\beta,\qquad
 \kappa_e=\frac{u\widetilde E_ev}{\lambda\,uv},
\tag{5}
\]
where \(\alpha\) starts at \(1^L\) and \(\beta\) selects the same terminal state. Here \(B>0\). Each \(\kappa_e>0\), because the hidden-free isolated insertion \(1^\infty e h^\infty\), followed by a boundary switch back to row 1, gives a positive marked bridge through this component.

Writing \(\widetilde R=(I-z\widetilde T)^{-1}\), the exact generating function is
\[
 \sum_{m\ge0}d_\pi(m)z^m
 =
 z^L\sum_{\sigma\in\mathfrak S_q}
 \alpha\widetilde R\,
 z\widetilde E_{\sigma(1)}\widetilde R\cdots
 z\widetilde E_{\sigma(q)}\widetilde R\beta.
\tag{6}
\]
The factor \(z^L\) accounts for the initial fixed collar; the terminal collar is already selected by \(\beta\). Expanding
\[
 \widetilde R(z)=\frac{\Pi}{1-\lambda z}
                +\text{a matrix analytic at }1/\lambda
\]
and using the rank-one identity gives
\[
 C_\pi^\partial
 =\lambda^{-L} B\prod_{e\in E_\pi}\kappa_e.
\tag{7}
\]
The \(q!\) chronological orders cancel the \(1/q!\) from the coefficient of the pole of order \(q+1\). More precisely, the relative error in (4) is \(O(1/m)\); all other exponential bases are strictly smaller.

Equations (4)–(7) do not claim that this collared class exhausts all equality words. A faster sea component might occur in words with different endpoints. The theorem supplies an unconditional product asymptotic for the entire collared class, including words with nearby double columns, rather than only for a separated-insertion subfamily.


