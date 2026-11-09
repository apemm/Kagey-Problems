# The split-residue construction: an obstruction and a corrected range proof

Research note, 8 November 2026. These are analytical results. They concern sufficient valuation conditions for excluding three-double right angles. They do not prove that the `1, x, h` family itself is impossible.

The source notation is `../2026-11-07/REPORT_1xh_construction.md`, especially Propositions 18, 24, and 25. Slots have horizontal coordinate `4j`.

## 1. The range argument in Proposition 24

Let three double points form a right angle at `(4j,r)`. Put

\[
 u=i-j,\qquad v=\ell-j,\qquad A=r_i-r,\qquad B=r_\ell-r.
\]

The right-angle equation and the completion row are

\[
 AB=-16uv,\qquad r+A+B\in[1,h].
\]

Assume that the tilted rectangle and its completion lie in the grid. All of `u,v,A,B` are nonzero. If `A,B` have opposite signs, the two leg endpoints give `|A|+|B|<=h-1`. If they have the same sign, the vertex and completion give the same inequality. Consequently

\[
 16|uv|=|AB|\le\frac{(h-1)^2}{4}=k^2,
 \qquad
 |u|,|v|\le R:=\left\lfloor\frac{k^2}{16}\right\rfloor.
\]

The sentence in Proposition 24 saying that the row differences always have opposite signs needs this replacement. The stated bound and proposition survive unchanged. The completion condition is essential when the row differences have the same sign.

Here is the exact sufficient condition underlying that proposition. For every pair of distinct odd rows assigned to slots at distance at most `R`, require

\[
 \tag{V}
 v_2(r_i-r_j)\le1+v_2(i-j).
\]

At an odd-row vertex, a leg to an even row has odd row difference. A leg to an odd row obeys (V). Thus the valuation of the product of the two row differences is at most

\[
 2+v_2(i-j)+v_2(\ell-j),
\]

strictly less than the valuation `4+v2(i-j)+v2(ell-j)` required by the right-angle equation. A leg with zero row difference cannot form a tilted right angle. This proves the desired exclusion.

The map in Proposition 24 satisfies (V): the distance bound puts two slots in the same block or adjacent blocks of length `kM`. Distinct residues modulo `M` retain their valuation below `v2(M)`. Equal residues either give the same row or a row-index difference of exactly `M`. This also justifies the binary-tree permutation version in Proposition 25.

## 2. Why the direct split of this mechanism fails

Write

\[
 h=8n+3,\qquad k=4n+1,\qquad q=k(k+1),\qquad n\ge1.
\]

Impose the complete slot rule of Proposition 18, with slots `0,...,q-1`. Its hot odd rows occupy even slots. Odd slots contain non-hot rows. Track A consists of slots `1 mod 4`, where the even row is `0 mod 4`; track B consists of slots `3 mod 4`, where the even row is `2 mod 4`.

The non-hot odd rows are exactly the rows `1 mod 8` and `3 mod 8`. Each residue class contains `n+1` rows, including the inert rows. There are `2n` even rows of class `0 mod 4` and `2n+1` of class `2 mod 4`.

There are `2n` hot odd rows. They use `2nk` even slots. Since there are `q/2=k(2n+1)` even slots, exactly

\[
 \tag{1} k=4n+1
\]

even slots remain available for edges through non-hot odd rows.

**Proposition A (global split obstruction).** No order satisfying the full slot rule can satisfy (V) for every pair of distinct odd rows on odd slots, without a distance restriction.

**Proof.** Two slots on opposite tracks have slot difference `2 mod 4`. If their distinct odd rows have the same residue modulo 8, their row difference has valuation at least 3. This violates (V), whose right side is 2. Therefore distinct rows of either one of the two non-hot residue classes cannot occupy opposite tracks.

Fix one residue class, containing `n+1` odd rows. If none of its rows occupies both tracks, all its rows that occur on odd slots must use one common track. Each of its rows must then put at least `2n` of its edges on even slots. The class uses at least `2n(n+1)` even slots.

If a row of the class occupies both tracks, every other row of the class has no odd-slot occurrence. Those `n` other rows require `nk=n(4n+1)>=2n(n+1)` even slots. A second row occupying both tracks is impossible.

Both residue classes together therefore need at least

\[
 \tag{2} 4n(n+1)>4n+1
\]

even slots. This contradicts (1). ∎

Thus applying the full inverse-valuation property only on odd slots does not resolve the conflict in Proposition 25. The track requirements create another counting obstruction.

## 3. A local obstruction at all heights at least 131 in this residue class

Proposition A alone does not block the actual mechanism of Proposition 24, since that mechanism needs (V) only within distance `R`. The following strengthens it to that setting.

**Window lemma.** Consider `2k+1` consecutive odd slots. Suppose distinct rows of the same residue modulo 8 cannot occur on opposite tracks within this window. Suppose also that each odd row occurs at most `k` times on the whole board. Then each of the two residue classes occupies just one track within the window.

**Proof.** If a residue class occupies both tracks, all its occurrences in the window must be one row. Call this a bridging class. If both classes bridge, the window contains at most `2k` points. If exactly one bridges, the other class occupies at most one track. The bridging row then fills every position on the other track, at least `k` positions, and occupies at least one position on the first track. That exceeds its total multiplicity `k`. The case where the other class is absent gives the same contradiction. Hence neither class bridges. ∎

**Proposition B (local split obstruction).** Suppose `h=8n+3>=131`. No order satisfying the full slot rule can satisfy (V) for all distinct non-hot odd rows on odd slots at slot distance at most `R=floor(k^2/16)`.

**Proof.** Here `k>=65`, so `R>=4k`. A window of `2k+1` consecutive odd slots spans `4k` slots. The valuation condition therefore gives the hypothesis of the window lemma. Each row occurs exactly `k` times on the full board, once for each even partner, so the multiplicity hypothesis also holds.

It follows that, in every such window, the two residue classes occupy separate tracks. Consecutive windows overlap in `2k` odd slots, including both tracks, so their track assignments agree. Thus the same assignment holds throughout the odd slots. Each of the `2n+2` non-hot odd rows must place at least `2n` edges on even slots, contradicting (1) and (2). ∎

This proof uses only the first relevant 2-adic level, not the higher levels of the proposed map.

**Corollary B1 (a contiguous core can cover at most about half the odd slots).** At the same heights, suppose the slot rule and the local inequality (V) hold only on an interval containing `N` consecutive odd slots, with `N>=2k+1`. Then

\[
 N\le k(n+1).
\]

**Proof.** The overlapping-window proof still forces each of the two non-hot row types onto one track throughout this interval. The type assigned to track A consists of `n+1` rows, each with only `2n` available even partners on that track. The other type has only `2n+1` partners per row on track B. Since each edge is used once,

\[
 N\le(n+1)\,2n+(n+1)(2n+1)=k(n+1).
\]

This proves the bound without any assumption on the doubles outside the interval. ∎

There are `k(2n+1)` odd slots on the full board. Thus a single such core must omit at least `kn` odd slots, a fraction `n/(2n+1)` of them. Short free transition regions cannot rescue the mechanism at these heights. The statement does not cover arbitrarily scattered exceptions or cores shorter than `2k+1` odd slots. It also leaves heights `11,19,...,123` open for a locally valid split map.

## 4. The analogous local obstruction for the even-row map

There is a related strengthening of the counting remark after Proposition 24. Write an even row as `2b+2`, with `b=0,...,k-1`, and suppose each index occurs `k+1` times. The direct even-row analogue is

\[
 \tag{E}
 v_2(b_i-b_j)\le v_2(i-j)
\]

for distinct values `b_i,b_j` and nearby slots.

**Proposition C.** For odd `k>=33`, no complete edge order can satisfy (E) for every pair of distinct even-row indices at slot distance at most `R=floor(k^2/16)`.

**Proof.** Distinct indices of the same parity cannot occupy opposite slot parities at distance at most `R`. Since `R>=2k+2`, apply the window lemma with multiplicity `k+1`, consecutive ordinary slots, and the two parities of `b`: every window of `2k+3` slots separates the two index parities by slot parity. Overlapping windows force a global separation. But the `(k+1)/2` even indices occur `(k+1)^2/2` times, more than the `q/2=k(k+1)/2` slots of either parity. ∎

This does not rule out an even-vertex construction using sizes, another modulus, or a weaker valuation argument. It does show that locality by itself cannot rescue the direct even-row inverse-valuation mechanism at large heights.

## 5. What remains possible

The obstruction is to a sufficient mechanism, not to valid boards. In particular, (V) is stronger than necessary. A pair that fails (V) need not participate in a right angle: the other leg, the exact product equation, and the completion must also exist. A useful next construction must exploit those missing conditions, relax the full hot-row slot rule, or protect only selected vertices and pairs.

The distinction is especially relevant for the proposed split: the results above block imposing the same pairwise leg inequality wholesale on the non-hot odd slots. They do not refute a split which uses different bounds for hot vertices, different row types, or different pairs of legs.

## 6. Independent finite checks

`check_split_obstruction.py` runs without third-party packages. It exhaustively checks the window lemma for multiplicity caps 1, 2, and 3, with three row labels of each type. There are respectively 36, 432, and 4,212 admissible windows, with no exceptions to the conclusion.

The same script enumerates the row differences and factor pairs in the corrected range argument through height 35. All 31,648 cases satisfy the bound. Exactly 15,824 cases have row differences of the same sign, confirming why the correction is needed. These computations check the proofs' elementary steps and do not certify a construction.
