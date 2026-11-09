# The absolute quadratic threshold: what random placement cannot do

Research note, 9 November 2026. The absolute bound m_0(h) = O(h^2) is not proved
here, and no lower bound above floor(h^2/4) is proved either. This note proves
three statements that locate the obstacle, and records which structured
placements were tried and why each one stops. It builds on
`full_problem_push/safe_triangle_pair_first_moment.md`,
`full_problem_push/two_moment_threshold_refinement.md` and
`full_problem_push/refined_scaffold_remaining_costs.md`. Nothing there is changed.

Notation. Q = floor(h^2/4), Lambda = 1 + log h. A label is a parity double
{a, b} with a odd and b even. A slot lattice is a set of columns delta Z with a
fixed delta whose even part divides 4 (the proved construction uses delta = 7 or 49).

## 1. Where the two logarithms come from

In the proved bound m_0(h) << h^2 Lambda^2 (loglog)^C the factor Lambda^2 enters
four separate times. Removing any one of them changes nothing.

| Source | Size of the budget | Nature |
| --- | --- | --- |
| Vertical rivals between two labels | Q Lambda^2 as a divisor majorant, Q Lambda as an exact count (Section 2) | genuine, independent of the sea |
| Label-root triangles in equal-residue blocks, and horizontal filler sides | Q Lambda^2 after the class sum | depends on the fixed sea profile |
| Three- and four-label supports | sqrt of a squared moment Lambda^4, hence Q Lambda^2 | upper budget; the three-label templates have true load Lambda^2 at full occupation |
| Dyadic private-weight classes | O(log h) blocks, each with collars of length O(h^2) | bookkeeping: Q Lambda in collars alone |

So an absolute bound needs all of: a constant number of blocks, a pair budget
O(Q), and a higher-arity budget O(Q).

## 2. Vertical rivals are a genuine load of order Q log h per label

**Proposition A.** Let a valid board have the parity double graph, and let its
labels sit on columns of a slot lattice delta Z. Let e = {a, b} have odd endpoint
a in [h/4, 3h/4]. There are at least c_delta h^2 Lambda pairs (f, g), with f a
label different from e and g a nonzero multiple of delta, such that no valid
board has e at a column x and f at column x + g. The cells outside these two
columns play no role. The same holds with the roles of the odd and even
endpoints exchanged.

**Proof.** Take coprime u > v >= 1 of opposite parity and an odd t that is a
multiple of the odd part of delta, with t(u^2 + v^2) <= h/4. Put

    g = 2tuv,   d = t(u^2 - v^2),   L = t(u^2 + v^2).

Then g^2 + d^2 = L^2. The numbers d and L are odd, and g is a multiple of delta
because uv is even. Put c = a + d, an even row, and r_- = a + (d - L)/2,
r_+ = a + (d + L)/2. All of c, r_-, r_+ lie in [a - L, a + L], inside the strip.
The rows r_-, r_+ differ by the odd number L, so {r_-, r_+} is a parity label.

Suppose e is at column x and a label f containing c is at column x + g. Let
M = x + g/2. The points A = (x, a) and C = (x + g, c) are black. The segment from
(M, r_-) to (M, r_+) has the same midpoint and the same length L as AC. So
A, (M, r_+), C, (M, r_-) is a rectangle. It is tilted because g and d are nonzero.

If column M is the double {r_-, r_+}, this rectangle is hidden, which a valid
board forbids. Otherwise let y be the column of the double {r_-, r_+}. The axis
rectangle with corners (M, r_-), (M, r_+), (y, r_-), (y, r_+) and the tilted
rectangle have corner sets whose symmetric difference is
{A, C, (y, r_-), (y, r_+)}. These four cells are black, so the two rectangles
have the same presentation whatever the colors of (M, r_-) and (M, r_+).
The board is invalid.

Distinct triples (t, u, v) give distinct pairs (g, d), since t = gcd(g, d) and
(2uv, u^2 - v^2) is the primitive pair. The number of triples is at least

    sum over coprime u > v of opposite parity with u^2 + v^2 <= h/(8 delta)
        of  c h / (delta (u^2 + v^2))   >=   c_delta h Lambda,

because the number of such (u, v) with u^2 + v^2 <= X is of order X. Each pair
(g, d), each sign of g, and each of the (h+1)/2 or so labels f containing c
gives a forbidden pair. This gives c_delta h^2 Lambda pairs. For the exchanged
roles, start from the even endpoint and use c = b - d. QED.

The upper bound O(Q Lambda) for the same count is equation (6) of
`refined_scaffold_remaining_costs.md`. So the vertical-rival load is exactly of
order Q Lambda per label, and the Q Lambda^2 divisor majorant overcounts it by
one logarithm.

**Corollary B (independent positions).** Place every label independently and
uniformly among N >= h consecutive slots of delta Z. For each label e with an
endpoint in the middle half of the rows, and each position of e at distance at
least h from both ends,

    P(e lies in no vertical rival | position of e)  <=  exp(-c_delta h^2 Lambda / N).

**Proof.** For different labels f the events "f sits at a forbidden offset from
e" are independent given the position of e, and each has probability
|G(e, f)|/N, where G(e, f) is the set of forbidden offsets. Proposition A gives
sum over f of |G(e, f)| >= c_delta h^2 Lambda. Multiply 1 - p <= exp(-p). QED.

Consequences, all for independent uniform positions.

1. With N = KQ and K constant, a label survives with probability at most
   h^(-c/K). So the answer to the alteration question is: the logarithmic load is
   a per-label load at every constant density, not only at full density.
   Deleting violated labels leaves a polynomially small fraction, and repeating
   the step needs h^(c/K) rounds.
2. Any proof that controls the expected number of violated events at a label
   (first moment, symmetric or product local lemma) needs N >= c Q Lambda,
   because the event family must contain the genuine events of Proposition A.
   Hence this method cannot give less than Q Lambda. The present Q Lambda^2
   could at best lose one logarithm.
3. Deleting a minimum vertex cover of the violation graph in place of all
   violated labels gains at most a factor of order log Lambda (Turan and the
   usual sparse-graph bound). I record this as a heuristic; it is not proved for
   this graph and would still leave a growing factor.

## 3. Which obstructions do not depend on the sea

**Proposition C.** In a valid parity board, the following configurations of
label cells are forbidden whatever the singleton cells are.

1. A vertical rival of two label points (Proposition A).
2. Three label points forming a tilted right angle whose fourth corner (x, r)
   lies in a double column. If r is one of that column's black rows, the
   rectangle is hidden. If not, the column contains a black row r' of parity
   opposite to r, the double {r, r'} occurs in some column y, and the axis
   rectangle on columns x, y and rows r, r' has the same presentation {(x, r)}
   as the tilted one.
3. A mixed side/diagonal collision whose four black cells are label cells.

If instead the fourth corner (x, r) of a three-label right angle lies in a
singleton column, the board stays valid exactly when that column's black row
has the parity of r and is different from r (Lemma 3.1 of `dominance_attempt.md`).

So a three-label right angle that completes in a sea column is a constraint on
one sea letter, not an obstruction. In a fixed periodic sea these events are
charged as violations, and they are the source of the Omega(log^2 h) three-label
load in `occupied_phase_three_label_incidence.md` only when the completion
column is occupied. This is the precise sense in which a jointly chosen sea
could remove the higher-arity logarithms: only families 1 to 3 are intrinsic.

## 4. Structured placements that were tried

Each rule below is aimed at family 1, the only intrinsic pair family.

* **Parity of the gap.** A vertical rival needs an even gap, since the white
  pair sits in the midpoint column. Three labels in one window always contain
  a pair at even gap, so parity alone protects at most two labels per window.
* **Two-adic spacing.** With gap g = 2y and d odd, a rival needs rs = y^2 with
  r, s of opposite parity and r + s < h. If 2^(2 v_2(g) - 1) > 2h this is
  impossible. A window of h columns in which every even gap has this property
  holds at most O(sqrt h) labels. This is the h^(5/2) identifying set again.
* **Size windows.** From L >= g + 1 and L >= |d| + 1, a pair is safe when
  d^2 <= 2g, or g^2 <= 2|d|, or g^2 + d^2 > (h-1)^2. Making all cross
  differences |c - a| small forces the odd and even endpoints of every label to
  be close, which covers only O(h^(3/2)) labels. Making them large fails for
  gaps between sqrt(2h) and h.
* **Star blocks.** Put the labels {a, c} with a fixed even row c in consecutive
  slots. The offsets forbidden around a label depend only on that label, and
  number about Lambda on average. Full occupation of the block is impossible,
  and leaving the forbidden slots empty returns density 1/Lambda. Filling them
  with labels of other stars needs a second arithmetic rule, which I could not
  find.
* **CRT and one-prime rules.** These remove right angles, and a global coloring
  removes vertical rivals in O(h^2) columns, but explicit mixed collisions
  survive (`continuation_crt_mixed_obstruction.md`), and the empty columns
  still need a sea.

## 5. Status and the missing statement

Proved here: Proposition A, Corollary B and its two rigorous consequences, and
Proposition C. Each was rechecked line by line: the parity of d, L and g; the
containment of c, r_-, r_+; the symmetric-difference identity; the injectivity
of (t, u, v) -> (g, d); and the independence used in Corollary B.

Not proved: m_0(h) = O(h^2), and any lower bound of the form c h^2 f(h) with f
unbounded. Proposition A is a statement about pairs of labels. It does not
bound the width from below, because it does not prevent a clever order.

The exact missing statement for an absolute bound in the present framework is
a deterministic slot map: an injection sigma from the labels into O(Q) slots of
delta Z such that

1. (delta (sigma(e) - sigma(f)))^2 + (c - a)^2 is never an odd square
   L^2 with L < h and the completion rows inside the strip, for a in e odd and
   c in f even;
2. no three-label right angle completes in an occupied column, and no
   four-label mixed collision occurs;
3. the labels form O(1) blocks, so the collar cost is O(Q).

Sea letters then have to satisfy the parity constraints of Proposition C and
the label-sea events of the chosen background. Random maps satisfy item 1 only
at density O(1/Lambda), by Corollary B. The arithmetic maps tried in Section 4
either lose a power of h or leave item 2 open.
