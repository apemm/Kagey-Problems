# Independent geometry audit of the entropy and square arguments

9 November 2026.

The all-odd sea entropy argument and the upper-half-prime boundary argument
pass the following collision-classification audit. The square codegree and
aggregate-budget arguments also pass. This note records the points where
extra forbidden-event types or boundary assumptions could otherwise be missed.

## 1. Four and six support cells suffice

For rectangles R,R', equality of presentations is equivalent to requiring
every point of their symmetric difference to be black. The colors of common
corners do not matter. Two distinct rectangles cannot share three corners.

- If they share no corner, each rectangle is hidden, so a hidden-rectangle
  event already detects the collision.
- If they share exactly one corner and that corner is black, they are again
  hidden. If it is white, the six remaining corners are distinct black
  support cells.
- If they share two corners, their four remaining corners form the support.
  This statement includes a common black corner and therefore includes
  configurations that might otherwise be mistaken for a separate five-cell
  event.

For a shared pair that is a side of both rectangles, the complementary
black sides form a hidden rectangle. For a pair that is a diagonal of both,
the two complementary diameters form a hidden rectangle. In the remaining
case the shared pair is a side of one rectangle and a diagonal of the other.

If the side is oblique, use the general mixed count. It must permit an axis
rectangle as the second rectangle. A horizontal side gives the horizontal
axis-rival count. A vertical side would require two black cells in one sea
column and is impossible.

Every event with two prescribed black cells in one column has probability
zero and can be discarded. Every remaining four-cell or six-cell event
specifies exactly four or six independent singleton variables, respectively.

## 2. Counts for the all-odd alphabet

A hidden tilted rectangle has primitive directions (u,v),(-v,u), with
u,v positive after choosing an orientation. Its integer side multipliers
are bounded by h/v and h/u. Summing over the vertical placement and these
parameters gives O(h^3 log^2 h) shapes modulo horizontal translation.

For an oblique mixed event, write the black side as alpha(u,v). Twice the
perpendicular midpoint displacement is beta(-v,u), with beta a nonzero
integer. The strip gives alpha<=h/|v| and |beta|<=2h/|u|. For each choice,
the alternative black diagonal is a lattice vector of the same squared
length. The divisor bound for representations as two squares contributes
h^epsilon, after adjusting epsilon. Thus the total is O(h^(3+epsilon)).

A horizontal rival is specified by three rows, plus a difference-of-squares
factorization L^2-x^2=(a-b)^2 with a!=b. Its count is again
O(h^(3+epsilon)).

For six support cells, label the black triples by their right-angle vertex.
Equality of the missing rows is one linear equation among six rows. This
leaves at most h^5 row tuples. With the common missing corner horizontally
anchored, each triple's two horizontal leg factors have a fixed nonzero
product. The divisor bound then gives O(h^(5+epsilon)) six-cell patterns.

With all black rows odd, a three-black tilted rectangle completes to an odd
row. Its singleton axis rival would need an even black row in that column,
which is absent. A vertical two-white completion has equal-parity endpoints,
so its row pair is absent from the parity double graph. These are the only
additional rivals introduced by treating the future full parity edge set as
available.

Consequently, an alphabet of k=ceil(h/2) odd rows has forbidden-event pressure
O(h^(-1+epsilon)). The four-cell and six-cell counts have the required powers
for the quantitative local-lemma estimate. No Sidon assumption is needed.

## 3. Boundary pins for the prime alphabet

Use rows 1+2p for all primes p=3 modulo 4 up to floor((h-1)/2), with row 1
outside a core of length greater than 2W_h. Every forbidden configuration
has horizontal span at most 2W_h. Hence all its row-1 pins lie in the same
tail.

A tilted rectangle has at most one corner on row 1. Thus a hidden four-cell
event has at most one pin. Fixing that row removes the vertical-translation
factor from its count.

A horizontal axis rival with two or more pins must have both complementary
axis-side cells on row 1. Its shared horizontal diagonal extends strictly
beyond the horizontal projection of both endpoints of the tilted black
diagonal. If a black-diagonal endpoint lies in the core, an axis-side pin
therefore lies beyond that core endpoint, contradicting the one-tail
condition. All-black-diagonal pins give a degenerate rectangle. Thus
horizontal rivals have at most one pin.

For an oblique mixed event, each complementary black pair has at most one
pin. The two-pin case is exactly the prime-anchor exclusion. That arithmetic
lemma does not require the alphabet to be Sidon or the primes to lie in a
narrow interval. It only uses distinct primes s,t, the divisibility
x | 2s(t-s), and the nonsquareness of -1 modulo s.

A six-cell event has at most two pins, one per tilted rectangle. In the
two-pin case, neither pin can be the right-angle vertex of its black triple:
both other vertices are above it and on the core side, so their dot product
is positive. The pins are therefore endpoint vertices. Equality of completion
rows reads

    1+c-b=1+f-e,    c-b=f-e!=0.

There are at most k^3 choices for these four free rows, without a Sidon
condition. The divisor count supplies the horizontal coordinates.

The rooted counts are consequently O(h^(2+epsilon)) for a one-pin four-cell
event, O(h^(4+epsilon)) for a one-pin six-cell event, and
O(h^(3+epsilon)) for a two-pin six-cell event. With k of order h/log h,
the total pressure is O(h^(-1+epsilon) log^6 h). This supports the claimed
canonical-component lower bound of order h/log h.

## 4. Square codegrees and sampling

For the six-cell hypergraph, the stated codegrees follow by splitting the
fixed vertices between the two black triples:

- Two fixed vertices in one triple give O(n) choices of its rectangle and
  O(n^2 log n) choices of the other rectangle. Splitting them between triples
  gives the same bound after summing over the common missing corner.
- For three fixed vertices, the 3+0 split fixes the completion and leaves
  O(n^2 log n) choices. The 2+1 split has O(n) completions and O(n) choices
  for each.
- For four fixed vertices, the 3+1 split leaves O(n) choices. In the 2+2
  split, a completion and the second fixed pair determine the second
  rectangle, so the total is still O(n).
- Five fixed vertices split as 3+2. Each rectangle is then determined up to
  a constant number of choices.

Thus Delta_2=O(n^3 log n), Delta_3=O(n^2 log n), Delta_4=O(n), and
Delta_5=O(1). For sampling probability n^(-0.79), the overlap-pair losses
relative to the expected number of vertices have powers -0.11,-0.32,
-0.53,-0.74. Deleting one point from each surviving pair with intersection
size at least two leaves a linear six-uniform hypergraph.

The independence estimate used afterward allows average degree and excludes
only two-cycles. This is stated in the primary
[Duke, Lefmann, and Rodl paper](https://onlinelibrary.wiley.com/doi/abs/10.1002/rsa.3240060208).
The resulting logarithmic improvement is consistent. If the resulting average
degree stays bounded, the elementary constant-degree bound is already stronger
than the target.

The overlapping dyadic-square argument in `square_progress.md` also checks.
At each scale L<4n, O(n^2/L^2) covering squares suffice, including scales
above n after enlarging the absolute constant. Every square of side ell is
contained in one with 2ell<=L<4ell. The threshold L^2/64 therefore gives
T_Q<=ell^2/4. The expected loss and the additional hidden-rectangle deletion
are smaller than the sample by a fixed small factor. The checkerboard
restriction supplies the claimed white-cell budgets.

That last construction controls aggregate budgets and hidden rectangles.
It does not ensure distinct presentations, and the report correctly states
this limitation.
