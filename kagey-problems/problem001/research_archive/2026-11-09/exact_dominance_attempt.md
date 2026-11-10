# Exact canonical dominance: a light-window criterion and the wall-sign obstruction

Research note, 9 November 2026. Exact dominance of the canonical component is not proved
here. This note proves a deterministic membership criterion for the canonical component,
derives the structural consequence for every competing component, and isolates the one
quantity that decides whether a Peierls argument for walls can work. It reads, and does
not modify, the notes in `full_problem_push/`.

**Corrections (added after audit).** Sections 6 to 8 contain statements that later audits
found false. They are left in place for the record and must not be cited.

* The codegree hypothesis of Proposition 9 is false by one factor of h. The tail bound
  itself survives with weaker proved codegrees; see
  `full_problem_push/exact_dominance_codegree_tail_audit.md`.
* The O(log^4 h) bound on mixed four-cell crossing mass is false: an explicit family has
  mass of order h. The correct statement is o(h log^2 h).
* The transverse scale l has weight 1/l^2, so its even part is 1/4, not 1/2. The corrected
  six-cell survival ratios are 15/17 (constant parity), 1/7 (checkerboards) and 13/16
  (quadratic phases), not the range 0.67 to 0.82 given here.
* The wall family has a logarithmically growing vertical-rival load, so the first-order
  expansion used here did not apply as written. The positive wall gain is proved, with a
  fixed collar of width O(h sqrt(log h)), in
  `full_problem_push/same_slope_wall_resolution.md`.

Theorem 1 (light pure windows are states of C_*) is unaffected and passes in
`full_problem_push/exact_dominance_light_bridge_and_quadratic_audit.md`.

Notation. Fix the parity partition and a large height h. W = 1 + floor((h-1)^2/4),
L = 2W. G is the sea graph with memory L, C_* its component containing the constant
states, lambda_* its Perron root. An affine law is X(x) = alpha x + beta (mod 2). A word
is pure for X on an interval if w_x = X(x) (mod 2) there. Lambda = 1 + log h.

Imported results, used as stated in their notes:

* (I1) Affine reduction and support family, `dense_residue_entropy_capture.md` sections 1
  to 3. In a word that is pure for one affine law, the forbidden events are exactly the
  normalized positive supports with four or six black cells. Every support has span at
  most L. With an anchor tail a_x in {1,2} of the same phase and dense residue buffer
  alphabets P_x (size h/8 + O(1)), no four-cell support has three or more tail pins, no
  six-cell support has five or more, and the total probability weight of tail-pinned or
  unpinned supports through one buffer column is delta_h = O(h^(-1/2+eps)).
* (I2) Global counts B_4 = O(h^(3+eps)), B_6 = O(h^(5+eps)) of normalized supports.
* (I3) The exact cut bound Z_X(n) <= exp(C h Lambda^2) r_X^n, from
  `protected_crossing_bulk_weight.md`, quoted in `continuation_domain_witness_frequency.md`.

## 1. Loads of a pure window

Let s be an allowed word of length L that is pure for an affine law X. Continue the law
to the right of s. Put a buffer of L columns after s, with alphabets P_x, and then the
anchor tail a_x^infinity of the same phase.

A support is s-pinned if it has at least one cell in s and at least one cell in the
buffer. It has no cell in the tail: the last column of s and the first tail column are
L + 1 apart, and a support has span at most L. Its buffer cells are called free.

For a buffer column x, let D_x(s) be the set of rows y in P_x such that some s-pinned
support has (x, y) as its only free cell and has all its other cells black in s. Put

    P'_x = P_x minus D_x(s),        p_x = 1/|P'_x|   (p_x = infinity if P'_x is empty).

For an s-pinned support F with at least two free cells, all of whose pinned cells are
black in s and all of whose free cells use letters of the reduced alphabets, put
wt(F) = product of p_x over its free columns. The right load of s is

    Lambda_R(s) = max over buffer columns x of
                  the sum of wt(F) over such F with a free cell in column x.

The left load Lambda_L(s) is defined by horizontal reflection, with a buffer and an
anchor tail to the left of s. Call s light if every P'_x is nonempty on both sides and

    Lambda_R(s) <= 1/100,     Lambda_L(s) <= 1/100.

and, on both sides,

    (A)  the sum, over the supports through any one buffer column that have no cell in s,
         of the product of p_x over their free columns is at most 1/100.

When |P'_x| >= |P_x|/2 in every buffer column, (A) holds automatically for large h: each
product is at most 2^6 times its full-alphabet value, and (I1) bounds the full-alphabet
sum by delta_h = o(1). Lightness is a finite, explicit condition on the word s alone.

## 2. Light pure windows are canonical states

**Theorem 1.** For every sufficiently large h, every light pure window is a state of C_*.

Proof. Consider the product space on the right buffer in which column x is uniform on
P'_x, independently. The word is s, then the buffer, then the anchor tail.

Every forbidden event that involves a buffer cell is of one of three kinds. (a) A support
with all its cells in the buffer and the tail. (b) An s-pinned support with one free
cell. (c) An s-pinned support with at least two free cells. No support meets both s and
the tail. Supports inside s do not occur because s is allowed, and supports inside the
tail do not occur because the tail is a valid sea. Since the whole word is pure for X,
(I1) shows that these are all the events.

Events of kind (b) have probability zero: their free letter was deleted. By (I1), no
event of kind (a) has exactly one free cell, so every remaining event has at least two
free cells. An event of kind (a) or (c) has probability at most the product of p_x over
its free columns, and zero if one of its free letters was deleted.

Give each event E of kinds (a) and (c) the weight x_E = 2 Pr(E). Two events are adjacent
when they share a buffer column. An event has at most six free columns. By (A) and the
load bound, the probability mass of events through one column is at most 1/50, so the
sum of x_F over the neighbours of E is at most 6 * 2 * (1/50) < 1/2. Hence

    Pr(E) <= x_E * product over neighbours F of (1 - x_F),

and the local lemma gives a positive probability that no event occurs. So there is a
buffer word u such that s u a^infinity is an allowed sea word. Its final L-window is an
anchor state, which lies in C_* by the adjacent-row two-shift. This is a path from s to
C_*.

The reflected argument gives an allowed word a^infinity u' s, hence a path from C_* to s.
A state with paths to and from a strongly connected component belongs to it. QED.

Audit notes. (1) The buffer has length L, so no support meets both s and the tail; this
is the only place where the buffer length is used. (2) Deleting letters can only remove
supports, and probabilities are computed for the reduced alphabets, so no event is
undercounted. (3) Common white corners of two rectangles need not be white for a support
to be forbidden; the support family of (I1) already uses that convention. (4) The proof
does not use any property of the past of s: the sea graph has memory L, so the state s
determines which continuations are allowed.

**Remark (frozen columns).** The definition allows |P'_x| = 1. Such a column behaves as a
pinned cell, and the load then measures the supports that it creates together with s.
Thus Theorem 1 already includes the device of freezing a heavily constrained buffer
column to a single allowed letter.

## 3. What a competing component must look like

**Corollary 2.** Let C be a recurrent component of the parity sea graph other than C_*.
Then no word read in C contains a light pure window. Equivalently, every window of length
L in every word of C either breaks every affine parity law or is heavy on at least one
side.

Proof. A light pure window is a state of C_* by Theorem 1, and distinct components have
disjoint state sets. QED.

**Corollary 3 (entropy target).** Let Y be the subshift of the sea shift in which every
light pure window is forbidden. If h_top(Y) < log lambda_*, then C_* is the unique
component of maximal entropy.

Proof. Every component other than C_* is contained in Y. QED.

Corollary 3 strengthens the gate-avoidance target of
`exact_canonical_gate_and_uniqueness_limits.md`, where only the single word 1^L is
forbidden: the forbidden family now contains all light pure windows of all four laws.

**Proposition 4 (average load).** Under the uniform product measure on the X-alphabets,
the expected number of deleted letters in a fixed buffer column is O(h^eps), and the
expected weight of the kind (c) events through a fixed buffer column, computed with the
full alphabets, is O(h^(-1+eps)).

Proof. A deleted letter needs a four-cell support with three pins or a six-cell support
with five pins. At most 4 B_4 + 6 B_6 normalized supports have a cell in a given column.
Their pinned cells are black with probability at most (2/h)^3 and (2/h)^5. By (I2) the
expectation is O(h^eps). For kind (c), a support with j >= 2 free cells and i pins
contributes (8/h)^j (2/h)^i (1 + o(1)), and i + j is 4 or 6. QED.

So loads are small on average: a typical pure window has about h^eps deleted letters per
column out of h/8. Proposition 4 does not show that a typical allowed pure window is
light. The window has L buffer columns on each side, and a first-moment bound gives
failure probability h^(-1+eps) per column, which a union over about h^2 columns does not
absorb. A stretched-exponential tail for the number of deleted letters in one column
would close this step. Since three pins determine the fourth cell of a four-cell support
up to O(1) choices, and five pins the sixth, h/16 deleted letters need a set of at least
c h^(1/5) pinned cells in special position, which suggests a tail of order
exp(-c h^(1/5) log h). I did not prove it.

## 4. Why a wall-by-wall Peierls argument does not close

By Corollary 2 and the capture theorem, a competitor uses windows that are impure or
heavy at spacing at most L. The natural plan is to show that each wall between two affine
laws multiplies the count by a factor below one, measured against the wall-free base.

**Lemma 5 (cross-wall mismatch).** Let the law be X_1 on columns x < 0 and X_2 on columns
x >= 0, with difference d(x) = X_2(x) - X_1(x) = a x + b (mod 2), not identically zero.
Let three black cells, each obeying the law of its side, form a tilted right angle with
completion cell Wc in the strip. The completion row disagrees with the phase of its
column exactly when

    the sum of d(x_c) over the corners c of the rectangle with x_c >= 0 is odd.

Proof. If all four corners used X_1, the corner parities would be consistent, because an
affine function satisfies X(x_A) + X(x_C) - X(x_B) = X(x_A + x_C - x_B). Replacing X_1 by
X_2 at the corners with x_c >= 0 changes the defect by the stated sum. QED.

By parity forcing, each such black triple is forbidden. There are two cases.

* Same slope (a = 0, b = 1; for example an odd-row sea next to an even-row sea, or two
  checkerboards of opposite phase). The triple is bad exactly when an odd number of the
  four corners lies across the wall.
* Different slopes (a = 1). A two-two split is bad when the two columns across the wall
  have an odd sum.

**Lemma 6 (same-slope walls have small triangle mean).** For a same-slope wall, the
expected number of bad cross-wall triples under the product measure is O(h Lambda).

Proof. Write the sides as alpha (u, v) and beta (-v, u) with u, v coprime and positive,
up to O(1) sign choices. The horizontal components are alpha u and beta v. If the sorted
corner columns are 0, a_2, a_1, a_1 + a_2 with a_2 <= a_1, the wall isolates exactly one
corner for at most 2 a_2 horizontal translations. Vertical containment gives
alpha <= h/v and beta <= h/u, so a_2 = min(alpha u, beta v) <= h min(u/v, v/u). Summing,

    sum over u, v of (h/v)(h/u) h min(u/v, v/u) <= 2 h^3 sum over u <= h of 1/u
                                                 = O(h^3 Lambda).

There are at most h vertical translations and each triple has probability at most
(2/h)^3 (1 + o(1)). QED.

For walls between different slopes, two-two splits are available for a number of
translations comparable to the span, and the same computation gives a mean of order h^2
when both sides are pure for about h^2 columns. Those walls are expensive.

**The obstruction.** For a same-slope wall, the triangle events can lower the count by at
most exp(-C h Lambda), by Lemma 6 and the local-lemma lower bound for sparse families.
The other change at a wall is in the universal four-cell and six-cell supports that cross
it. Their rows must now match two different parity classes on the two sides, so the set
of compatible crossing supports differs from the one-law case. By (I3) the total crossing
weight is O(h Lambda^2) in either case. Hence the logarithm of the exact wall factor is

    - (triangle term, at most C h Lambda)
    - (crossing weight with the wall minus crossing weight without it, O(h Lambda^2)).

The second term has a larger order than the first and its sign is not known. If the
crossing weight is smaller with the wall, at leading order h Lambda^2, a same-slope wall
is an entropically favourable interface, and no Peierls bound can hold for it. If it is
larger, the Peierls bound holds with room to spare. Route B therefore reduces to one
asymptotic computation: the leading coefficient, at order h Lambda^2, of the crossing
weight of mixed four-cell supports across an odd/even wall and across an opposite-phase
checkerboard wall, compared with the one-law crossing weight. The methods that gave the
mixed-support ratios 13/16 and 5/4 between protected phases are the natural tool.

A favourable sign would not refute dominance. It would mean that a competitor cannot be
excluded by counting, and that the bridge of Theorem 1 has to be extended to windows that
contain walls.

## 5. Status

Proved here, for the parity partition and large h, given (I1) to (I3):

1. Theorem 1: light pure windows are states of C_*.
2. Corollaries 2 and 3: competitors avoid every light pure window, and dominance follows
   from an entropy bound for the subshift that forbids them.
3. Proposition 4: loads are O(h^eps) letters per column on average.
4. Lemmas 5 and 6: the exact mismatch rule at a wall, and the O(h Lambda) bound on the
   triangle mean of a same-slope wall.

Not proved: exact dominance; that typical allowed pure windows are light; any sign for
the wall factor. The quadratic partitions were not treated; Theorem 1 should transfer
with the four quadratic phases in place of the affine laws, but I did not check the
pinned counts there.

Stuck point. Two independent gaps remain.

(G1) A tail bound exp(-omega(log h)) per column, strong enough for a union over 2L
columns, for the number of buffer letters deleted by a pure allowed window. This would
show that almost every allowed pure window is light, and it is needed before Corollary 3
can be compared with the single-law entropy.

(G2) The sign of the leading h Lambda^2 term of the crossing-weight difference at a
same-slope wall. Without it, neither direction of the wall comparison is available, and
Corollary 3 cannot be converted into an inequality for h_top(Y).

## 6. The sign at a same-slope wall (gap G2)

This section computes the leading change of the crossing support mass at a wall. The
parity statements are proved. The mass comparison is a leading-order lattice count: the
direction densities are exact, but I did not control the error terms, so the conclusion
is stated as a computation to be audited, not as a theorem.

**Lemma 7 (parity sums).** In every mixed four-cell support the four black rows have even
sum. In every hidden rectangle the four rows have even sum. In every six-cell support
(two rectangles sharing exactly one corner X) the six black rows have even sum.

Proof. For a mixed support with black side A, B, black diagonal C, D and U = B - A, the
shared white points are (C + D -+ U)/2. Integrality gives y_C + y_D = U_y = y_A + y_B
(mod 2). A hidden rectangle has equal opposite-corner row sums. In a six-cell support
both black triples have the same completion row, so y_A + y_C - y_B = y_D + y_F - y_E. QED.

**Corollary 8.** At a same-slope wall (law difference d = 1 on one side), a universal
support is compatible with the two alphabets only if an even number of its black cells
lies beyond the wall. For a six-cell support, either each of its two rectangles has an
even number of corners beyond the wall, or each black triple is already a forbidden
cross-wall triangle of Lemma 5 and the six-cell support is redundant.

So a same-slope wall deletes every crossing support with an odd split, keeps a family of
even splits with changed row parities, and adds the triangle events of Lemma 6.

**Which family carries the cut mass.** For six-cell supports, fix the common corner X and
write one rectangle as X, X + S, X + T, X + S + T with S = alpha (u, v), T = beta (-v, u),
gcd(u, v) = 1. Vertical containment gives alpha v, beta u <= h. A direct count of pairs of
such rectangles through X, weighted by the number of cut positions, gives crossing mass

    W_6 = Theta(h Lambda^2),

carried by long thin rectangles (u large, v small, horizontal extent alpha u up to about
h^2). The mixed four-cell supports have crossing mass O(Lambda^4): a support of extent
above h needs its black diagonal within angle h/|U| of horizontal, and this factor
cancels the extent. Hence the cut bound (I3) is governed by six-cell supports.

**Direction densities.** For a long thin rectangle the sorted corner columns are
X, X + T close together, then X + S, X + S + T close together. A cut in the long gap
gives the split {X, X+T} | {X+S, X+S+T}. Row conditions:

* one law on both sides: S_y and T_y even, that is alpha v even and beta u even;
* odd/even wall in the long gap: S_y odd and T_y even, that is alpha v odd and beta u even.

For primitive (u, v), the densities of admissible (alpha, beta) are

    (u, v)        one law     wall
    (odd, odd)    1/4         1/4
    (even, odd)   1/2         1/2
    (odd, even)   1/2         0

The extent-weighted number of directions is proportional to phi(v)/v^3. With
a = sum over odd v of phi(v)/v^3 and b = sum over even v, the Euler factor at 2 of
zeta(2)/zeta(3) is 7/6, so a = 1.1729 and b = 0.1955 to four places. The one-law mass is
proportional to (3/8) a + (1/2) b = 0.5376 and the wall mass to (3/8) a = 0.4398. A long
rectangle cut in its long gap survives at an odd/even wall with relative density

    1 - kappa,      kappa = 0.182.

A crossing six-cell support has one or both rectangles cut, so its surviving mass is
theta W_6 with (1 - kappa)^2 <= theta <= 1 - kappa.

For two checkerboards of opposite phase the conditions are alpha (u + v) even (one law)
and odd (wall), with beta (u + v) even in both. The (odd, odd) directions carry density 1
with one law and 0 at the wall, and kappa = 0.75.

**New unfavourable terms at an odd/even wall.**

* Cross-wall triangles: mean O(h Lambda), Lemma 6.
* Cross-wall vertical rivals. Two black cells on opposite sides with even horizontal gap
  2d, odd row difference e, and (2d)^2 + e^2 = l^2 with l odd have a vertical white pair
  of odd length, which is a parity edge. This two-cell event does not occur inside one
  law. Its mean is at most the sum over such triples of 2d (h - l)(2/h)^2, which is
  O(h Lambda) because there are O(h Lambda) triples with l <= h.

**Net wall log-weight (computed, not audited).** For a wall whose two sides are pure for
at least 2W columns,

    log(wall factor) = + (1 - theta) W_6 (1 + o(1)) - O(h Lambda),
    (1 - theta) W_6 >= kappa W_6 = Theta(h Lambda^2).

The four/six-cell change is favourable and has the larger order. So a same-slope wall is
an entropically favourable interface for large h, and Route B does not exist for these
walls. The resulting rate gain is of order Lambda^2/h per column in the logarithm, which
is order log^2 h in the rate. This is the same order as the proved slack
0 <= R_h - r_Q <= C log^2 h (1 + log log h)^2 in the full-problem report, which is a
consistency check on the order and the sign.

**Odd h.** The even-row phase has (h - 1)/2 letters against (h + 1)/2. An even domain of
length n costs exp(-2n/h (1 + o(1))) against an odd domain, which is O(h) for n of order
h^2 and is below the wall gain Theta(h Lambda^2). The sign is unchanged; the optimal
domain lengths become unequal.

**Different slopes.** By Lemma 5 a two-two split is bad when the two columns beyond the
wall have odd sum, which holds for the long gap of a positive fraction of directions. The
bad triple mean is of order h^2 when both sides are pure for about h^2 columns. This
exceeds every available gain, which is O(h Lambda^2). These walls are unfavourable, as
expected.

Audit notes. (1) Lemma 7 and Corollary 8 are exact. (2) The density table is exact.
(3) The claims W_6 = Theta(h Lambda^2) and mixed crossing mass O(Lambda^4) are
order-of-magnitude counts; the first agrees with (I3). (4) The comparison ignores the
short end gaps of the rectangles, whose mass is O(h Lambda) by the computation of
Lemma 6. (5) Converting masses into a factor uses a first-order avoidance expansion for
the crossing family with relative error o(1); the full-problem notes prove such
expansions for protected phases, not yet for a wall.

## 7. A tail bound for deleted letters (gap G1)

Let N_x be the number of letters deleted in buffer column x by a pure window s.

**Hypothesis (uniform codegrees).** For r = 4 and r = 6, for every set of j cells with
1 <= j <= r - 2, and every column x, the number of r-cell supports that contain these
cells and have a further cell in column x is at most C_eps h^(r - 2 - j + eps).

For r = 4 the case j = 2 is proved: three cells of a hidden rectangle determine the
fourth, and three cells of a mixed support determine the fourth up to two choices (a line
meets a circle), so two fixed cells and a column leave at most O(h) supports. The case
r = 4, j = 1 is the row-uniform form of (I2). For r = 6 I checked only j = 4 with a full
triple fixed. The remaining cases are assumed.

**Proposition 9.** Assume the hypothesis. Under the uniform product measure on the
X-alphabets, and under the uniform measure on allowed pure windows,

    Pr(N_x >= h^(5/6 + eps)) <= exp(-c h^(1/6) log h)

for every buffer column x. Consequently, with probability at least
1 - exp(-c h^(1/6) log h) for a smaller c, no buffer column on either side loses more
than h^(5/6 + eps) of its h/8 letters.

Proof. A witness for a deleted letter is the pin set of a support with one free cell in
column x. Put k = h^(1/6).

Level 0. The expected number of realized witnesses is mu = O(h^eps). The probability
that k pairwise disjoint witnesses are realized is at most mu^k/k!. Otherwise a maximal
disjoint family has fewer than k members, and every realized witness meets its cell set
T_0, of size at most 5k.

Level j. Fix j black cells c_1, ..., c_j. By the hypothesis, the expected number of
realized witnesses containing them, counted by their remaining pins, is O(h^eps). Either
k of them are disjoint outside the fixed cells, with probability at most
(C h^eps)^k / k!, or all of them meet a set T_j of at most 5k further cells.

At the last level all pins but one are fixed. The remaining pin ranges over O(h)
candidates, each black with probability 2/h, and each determines the free cell up to
O(1) choices. More than k realized candidates has probability at most (C/k)^k.

On the complement of all the exceptional events, every deleted letter is reached by a
chain c_1 in T_0, c_2 in T_1(c_1), and so on, so N_x <= C k^5. There are polynomially
many chains and levels, and each exceptional event has probability at most
exp(-c k log k). This proves the bound for the product measure.

For the uniform measure on allowed pure windows, the conditional form of the local lemma
bounds the probability of any assignment of t cells by C^t times its product
probability, as in (5) and (6) of `continuation_changed_black_letter_suppression.md`.
Every estimate above is a sum of probabilities of assignments of at most 5k cells, so
each acquires a factor C^(5k), which the factorials absorb. The union over the 2L buffer
columns costs a factor h^2. QED.

The same scheme applies to the weighted load of events with at least two free cells; I
did not write that case out. With it, almost every allowed pure window is light.

Audit notes. (1) The product-measure bound is not small against the probability
exp(-C h Lambda^4) that a window is allowed, so the conditional form is needed, and the
proof uses it. (2) Proposition 9 concerns the fixed-phase measures. It gives no
information about the Perron measure of a hypothetical competitor: by a
Donsker-Varadhan comparison, an entropy deficit of order h Lambda^4 per window exceeds
the exponent h^(1/6) of the tail.

## 8. Assembly

**What is proved.** Theorem 1 and Corollaries 2 and 3; Lemmas 5, 6, 7 and Corollary 8;
Proposition 9 under its hypothesis.

**What the wall computation changes.** If section 6 is confirmed, the statement
"a competitor must contain walls or defects every L columns, and walls cost entropy" is
false in its second half. The picture becomes:

1. The words of largest growth for the parity partition are not pure. They carry
   same-slope walls at spacing of order h^2, each worth exp(+c h Lambda^2).
2. This does not create a second component. A word with two walls more than L apart has a
   pure window between them, and if that window is light it is a state of C_*. So every
   wall lattice of spacing above L, with typical fillings, lies in C_*, and lambda_*
   exceeds every pure rate by a factor exp(c Lambda^2/h).
3. A competitor must therefore avoid light windows while matching this rate. The gain per
   column from a lattice of spacing n is about (1 - theta) W_6(n)/n, where W_6(n) is the
   cut mass of supports of extent at most n, minus O(h Lambda)/n. Since W_6(n) is roughly
   linear in n up to h^2, the gain is nearly flat in n between h Lambda and h^2. Whether
   the optimal spacing is above or below L = 2W is not decided by the leading order.

**Conditional theorem.** Suppose that, for the parity partition and all large h, every
recurrent component C with rho(C) >= lambda_* contains an allowed window, of any phase
pattern, for which the pinned event system of a law-continuing buffer and anchor tail
satisfies the local lemma condition of Theorem 1 on both sides (a light window in the
general sense, with the cross-wall triangles and vertical rivals added to the event
list). Then C = C_*, and C_* is the unique component of maximal entropy. The proof of
Theorem 1 applies verbatim, because it uses only the list of events that involve a
buffer cell and the memory-L property.

**Exact stuck point.** The hypothesis of the conditional theorem. Fixed-phase measures
have light windows with overwhelming probability (Proposition 9), but a competitor's
Perron measure is only known to be within entropy O(Lambda^4/h) per column of a
fixed-phase measure, and that is far too weak to transfer a local tail bound of exponent
h^(1/6). A proof needs one of:

(a) a bounded-density property for near-maximal components: every assignment of t <= h^c
    cells has Perron probability at most C^t (2/h)^t. This would transfer Proposition 9
    directly;
(b) an exact description of the optimal wall lattice, showing its spacing exceeds L, so
    that any component of maximal rate has pure windows of length L, followed by (a)
    restricted to those windows;
(c) a bridge that does not need lightness: a deterministic construction of an exit from
    an arbitrary state, which the explicit dead-end and failed-exit examples show must
    depend on the past.

For the quadratic partitions, which carry the true maximum R_h, none of sections 1 to 7
has been checked. The parity sums of Lemma 7 hold for any partition, but the compatible
splits at a wall between quadratic phases follow a different rule.
