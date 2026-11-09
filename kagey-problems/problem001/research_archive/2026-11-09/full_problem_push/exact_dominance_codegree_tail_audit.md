# Corrected codegrees and the missing light-window tail

9 November 2026. This note audits Section 7 of
[exact_dominance_attempt.md](../exact_dominance_attempt.md), without
changing that source. Its stated codegree hypothesis is false by one
power of h. The weaker, already proved codegrees suffice for Proposition
9 and also give the omitted tail for events with several free cells.
The moment argument and the final lightness implication have passed a
separate independent review.

For the parity partition, one fixed affine phase, and sufficiently
large h, use the source's established protected support family and
same-phase anchor bounds. A uniformly chosen normalized allowed
pure window is light with probability

    1-exp[-c_epsilon h^(1/6) log h].

This is a fixed-phase statement. It does not transfer that conclusion
to the Perron measure of an arbitrary competing component.

## 1. A counterexample to the stated hypothesis

Fix the two black cells C=(2,1), D=(8,9), and the further column x=10.
For every odd c in [1,h] except c=5, put

    B=(0,c), A=(10,c), P=(0,5), Q=(10,5).

The rectangle with black diagonal CD and white diagonal PQ is tilted:
both diagonals have midpoint (5,5) and squared length 100. The rectangle
ABPQ is axis aligned and nondegenerate. Their symmetric difference is
exactly {A,B,C,D}.

There are Theta(h) distinct four-cell supports containing the fixed
cells C,D and a further cell in column 10. All four black columns are
distinct and all rows are odd. The three pins B,C,D lie strictly to
the left of the free column A. Thus the failure persists in the
one-sided buffer setting, not just for an unconstrained column.

[verify_deleted_letter_codegree_counterexample.py](verify_deleted_letter_codegree_counterexample.py)
checks this exact family at five heights; its output is
[deleted_letter_codegree_counterexample_check.json](deleted_letter_codegree_counterexample_check.json).

The asserted h^epsilon bound at r=4,j=2 cannot hold. Scaling both
coordinates by four, and translating rows to keep them positive,
also puts the entire certificate in one common coordinate residue
class. The issue is not a parity incompatibility.

The correct exponents are

    M_(r,j) <= C_eta h^(r-1-j+eta),  1<=j<=r-2,
    M_(r,r-1) <= C,                 r in {4,6}.

Here prescribed cells occupy distinct columns, as required for a sea
word. M counts all supports containing those cells. Asking for an
additional cell in a specified column only decreases the count.
The j=0 version for supports through one specified column is
C_eta h^(r-1+eta).

These bounds are proved in
[crossed_codegree_and_avoidance.md](crossed_codegree_and_avoidance.md),
Section 2. In particular, two crossed fixed points of a mixed support
have O(h^(1+eta)) completions by its divisor calculation. For six
supports, distribute prescribed cells between the two triples: a full
triple fixes the shared corner; a fixed pair gives O(h) possible
rectangles; and two fixed pairs have O(h) possible shared corners even
when their completion loci coincide. Five prescribed cells determine
the last cell up to an absolute number of choices.

These are precisely the bounds needed below. After j pins have been
fixed, a one-free-cell support still has r-1-j random pins, so its
weighted conditional degree is O(h^eta), not O(h^(-1+eta)).

## 2. Assignment domination under the two window measures

Let nu be either the independent protected product measure on a window,
or its conditional law given that the window avoids every normalized
protected forbidden support. There is an absolute constant C_0 such that
every compatible assignment T of cells in distinct columns satisfies

    nu(T is black) <= (C_0/h)^|T|.                 (1)

For the product measure this follows from alphabet sizes h/2+O(1).
For the allowed-window measure, use the arbitrary-event conditional
local-lemma inequality. The full protected bulk has o(1) incident
probability at each column. Avoiding it therefore increases the
probability of a t-cell assignment by at most exp(o(1)t), uniformly in
the assignment and the window length. This proves (1), after increasing
C_0. Incompatible assignments have probability zero.

This is conditioning on avoidance of the protected event family. It is
not an assertion about conditioning on an arbitrary exterior word.

## 3. A moment device for pin families

Put p=C_0/h. Let

    Z=sum_F alpha_F 1_(A_F is black),

where A_F is a set of at most d pins and alpha_F>=0. Expand Z^k as a
sum over ordered k-tuples of supports and apply (1) to their union.
For any already exposed compatible union T, the factor from the next
support is

    alpha_F p^|A_F minus T|.

Group this sum by J=A_F intersect T. If the sum for each specified J
is at most D, then, since |T|<=dk,

    E_nu Z^k <= [C_d (1+dk)^d D]^k.              (2)

This follows by summing the next support first at each step. There are
at most sum_(j=0)^d binom(|T|,j) choices of J. Incompatible choices can
be omitted. No independence between successive supports is assumed.

All applications below use a bounded number of arity and pin-count
classes. They can be treated separately and then combined by a finite
union bound.

## 4. Deleted-letter tail without an assumed codegree

Fix a buffer column x. Let X_x count realized supports whose only free
cell lies in x. Counting supports instead of distinct deleted letters
only increases the random variable, so N_x<=X_x. Such a support has
r-1 pins, at most five.

For a specified set J of j exposed pins, the corrected codegree gives

    sum_(F with A_F intersect T=J) p^(r-1-j)
      <= C_eta h^eta.                            (3)

For j=0 use the column-rooted global count. For j=r-1 use the constant
completion bound. Thus (2), with d=5 and alpha_F=1, gives

    E_nu X_x^k <= [C_eta k^5 h^eta]^k.           (4)

Fix 0<epsilon<1/6, choose eta<epsilon, and put
k=floor(h^(1/6)). Markov's inequality at h^(5/6+epsilon) gives

    nu(N_x>=h^(5/6+epsilon))
      <= exp[-c_epsilon h^(1/6) log h].          (5)

Indeed the ratio inside the k-th power is at most
C_eta h^(eta-epsilon), which is a negative fixed power of h for
large h. This proves the claimed tail under both measures, using the
weaker true codegree and no sunflower selection.

## 5. Tail for the multi-free-cell load

First compute load using the full buffer alphabets P_x. Write Y_x for
the sum of full-alphabet probabilities of all s-pinned supports that
have at least two free cells and use x as a free column. A support of
arity r has i pins and f=r-i free cells, where 1<=i<=r-2<=4. Its
coefficient alpha_F is at most (C_1/h)^f because |P_x|=h/8+O(1).

For j prescribed pins, including the case j=i, the corrected codegree
implies

    sum_(F with A_F intersect T=J) alpha_F p^(i-j)
      <= C_eta h^(r-1-j+eta) h^(-f) h^(-(i-j))
      <= C_eta h^(-1+eta).                       (6)

The j=0 bound again uses the column-rooted global count. Therefore
(2), with d<=4, gives

    E_nu Y_x^k <= [C_eta k^4 h^(-1+eta)]^k.      (7)

Take k=floor(h^(1/6)) and, for example, eta=1/12. The factor k^4
h^(-1+eta) is O(h^(-1/4)). At every fixed threshold a>0,

    nu(Y_x>a) <= exp[-c_a h^(1/6) log h].        (8)

This supplies the multi-free-cell load tail omitted from the source.

On the event in (5), every reduced alphabet eventually has at least
half its original letters, because epsilon<1/6. Passing from full
to reduced alphabets increases any support weight by at most 2^6.
Taking a=1/(100*2^6) in (8) therefore makes the reduced pinned load
at most 1/100. The source's imported unpinned/tail bound also increases
by at most 2^6 and remains o(1), so condition (A) holds for large h.

There are O(h^2) buffer columns on both sides. A union bound over them
only changes the constant in the stretched-exponential estimates.
Hence an allowed pure window is light with probability at least

    1-exp[-c_epsilon h^(1/6) log h].             (9)

## 6. What this repairs, and what remains open

The written uniform codegree hypothesis is refuted, but Proposition 9's
conclusion and the missing load estimate follow from existing true
codegrees. Together with the source's deterministic light-window
criterion, (9) puts almost every allowed pure window in the canonical
component, under that fixed-phase uniform measure.

This does not prove exact canonical dominance. The source correctly
identifies the remaining gap: there is no comparable assignment bound
for the Perron measure of an arbitrary competing component. Nor does
this audit validate Section 6's wall-pressure expansion or transfer
the parity anchor theorem to other row partitions.

The counterexample and the moment argument are recorded separately
from the user's source. No change to that source is required to inspect
the correction.
