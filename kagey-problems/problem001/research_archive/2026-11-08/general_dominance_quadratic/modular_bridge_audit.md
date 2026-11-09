# Modular sea audit and limits of bounded repairs

8 November 2026. The modular-sea and three-black-corner propositions in
[dominance_bridge.md](dominance_bridge.md) pass independent proof review. The
proposed constant splice fails at height 37, before the height-43 example in
that note. A separate extension lemma makes this a failed prescribed exit at
every height at least 37. None of these failures establishes a second recurrent
component.

All row coordinates in this note are zero-based.

## 1. Audit of the two propositions

Proposition 1 correctly proves validity of the modular sea

\[
 y_x\equiv cx\pmod p,\qquad 0\le y_x<p,
 \qquad \chi_p(1+c^2)=-1
\]

for every partition at height \(p\). In the mixed-collision argument, the bound
\(|T_y|<p\) can be read directly from
\(T_y=(A_y+B_y-C_y-D_y)/2\). It follows from the black rows alone. This
observation is useful when the ambient strip becomes taller.

Proposition 2 also holds as stated. Its three-black family has a white missing
corner exactly two rows below the black point in that column. The family has
distinct missing corners. Its vertical and horizontal pair exclusions are
valid. These conclusions leave mixed collisions unresolved, and those
collisions invalidate the proposed splice.

## 2. A mixed collision with only one tail point at height 37

Let

\[
 w_x=\begin{cases}x\bmod37,&x<0,\\35,&x\ge0.\end{cases}
\]

Consider the black pairs

\[
 A=(-46,28),\quad B=(3,35),\qquad
 C=(-37,0),\quad D=(-2,35),
\]

and the white pair

\[
 P=(-44,14),\qquad Q=(5,21).
\]

Only \(B\) is in the constant tail. The other three black coordinates satisfy
their modular row condition. The two white coordinates are white because the
actual black rows at their columns are 30 and 35.

The sets \(R_1=\{A,B,P,Q\}\) and \(R_2=\{C,D,P,Q\}\) are distinct tilted
rectangles. For the first,

\[
 B-A=Q-P=(49,7),\qquad A-P=(-2,14),
 \qquad (49,7)\cdot(-2,14)=0.
\]

For the second, the two diagonals have equal midpoint and equal length:

\[
 C+D=P+Q=(-39,35),\qquad
 |D-C|^2=35^2+35^2=2450=49^2+7^2=|Q-P|^2.
\]

The diagonal directions are neither parallel nor axis-parallel, so the second
rectangle is also nondegenerate and tilted. Every listed row is between 0 and
36. Both white presentations are exactly \(\{P,Q\}\). This proves failure
independently of any partition or axis-rival test.

The targeted search [check_modular_mixed.py](check_modular_mixed.py) produced
this certificate. Its scope is the mixed-collision case with three ramp points
and one tail point. It found no such collision for
\(p=3,5,11,13,19,29\), then stopped at this certificate. Those smaller checks
are not complete splice-validity checks. The output field
`complete_one_tail_case` means the decision search returned a witness or
exhausted its case, rather than that all witnesses were enumerated.

The height-43 certificate in Section 4 of `dominance_bridge.md` also passes
independent verification. It uses two tail points and has diagonal squared
length 5200. The two examples therefore expose different distributions of the
four black points across the interface.

## 3. Modular seas remain valid in a taller parity strip

**Band extension lemma.** Let \(p\) be an odd prime and
\(\chi_p(1+c^2)=-1\). Place the modular sea in any band of \(p\) consecutive
rows of a strip of height \(h\ge p\). There is still one black point in each
column. The resulting sea is valid for the parity partition of the larger
strip.

**Proof.** Translate the band vertically so its black rows lie between 0 and
\(p-1\). The ambient strip can extend past these two rows. All black-point
differences still obey

\[
 U_y\equiv cU_x\pmod p,\qquad |U_y|<p.
\]

The original dot-product argument therefore excludes three black corners,
hidden rectangles, and singleton presentations. The same-side and
same-diagonal collision reductions still produce a hidden rectangle. In a
mixed collision, put \(2T=A+B-C-D\). Then \(|T_y|<p\), irrespective of the
ambient height. The original modular perpendicularity argument excludes the
mixed case and oblique axis rivals unchanged.

It remains to reconsider horizontal and vertical presentations. If a black
diagonal \(U\) has integral length \(d\), nonresiduosity gives

\[
 p\mid U_x,d,\qquad U_y=0.
\]

A horizontal white diagonal would coincide with this black diagonal. A
vertical white diagonal can now fit in the enlarged strip. Its center is at
the common integral row of the two black endpoints, so its endpoints are
integral only if \(d\) is even. Its two rows then have the same parity, and it
has no parity axis rival. All other collision mechanisms have already been
excluded. Vertical translation of the band changes none of these arguments.
\(\square\)

The parity hypothesis in the enlarged strip is essential to this proof.
It does not assert validity for every partition after enlargement.

**Infinite-height consequence.** The height-37 periodic ramp is a valid
recurrent parity sea in every strip of height \(h\ge37\). The prescribed
constant exit to row 35 still has the two rectangles from Section 2. Thus a
single modular example gives failed prescribed exits at infinitely many
heights. This does not assert failure of every constant row or every phase,
and it does not rule out longer bridges to the boundary component.

## 4. What a bounded repair could prove

Let \(L\) be a valid memory length, and let \(C_*\) be the canonical component
of the full length-\(L\) sea graph. A word carried entirely by another recurrent
component \(D\) shares no length-\(L\) block with a word carried by \(C_*\).
Such a block is itself a full-history state, and distinct components have
disjoint state sets.

This gives a limitation stronger than the failure of immediate constant
padding.

**Edit lower bound.** Suppose a length-\(n\) word carried by \(D\ne C_*\) is
converted into a word carried by \(C_*\) using \(K\) insertions, deletions, or
substitutions. Then

\[
 n\le KL+L-1,
 \qquad
 K\ge\left\lceil\frac{n-L+1}{L}\right\rceil.
\]

**Proof.** A sequence of \(K\) edits divides the unchanged letters into at
most \(K+1\) common contiguous runs. Each run has length at most \(L-1\),
since a common run of length \(L\) would give a common state. At most \(K\)
original letters were deleted or substituted. Consequently
\(n\le K+(K+1)(L-1)\). \(\square\)

A bounded-edit conversion of all recurrent words into canonical words would
therefore prove that no other recurrent component exists. The monotone bridge
theorem does not yet supply such a conversion. Sorting arbitrary rows into a
monotone word also cannot retain bounded information: there are only

\[
 \binom{n+h-1}{h-1}
\]

nondecreasing words of length \(n\), a polynomial in \(n\) for fixed \(h\).
Any positive-entropy input language would have exponentially large fibers
under such a map, even before checking whether its output is valid.

A more general encoding could still compare entropy. For example, maps from
all length-\(n\) words of a component into canonical words of length
\(n+o(n)\), with \(\exp(o(n))\) preimages per output, would prove
\(\rho_D\le\rho_*\) by counting. This is a sufficient criterion, not a
constructed map, and it gives a non-strict comparison only. No such general
encoding or arbitrary-past bridge has been proved here.
