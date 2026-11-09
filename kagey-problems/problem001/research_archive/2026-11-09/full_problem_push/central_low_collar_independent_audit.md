# A central low collar at an ordinary same-slope wall

9 November 2026. The two-sided pinned-event estimates needed for the proposed ordinary-parity collar hold, with one correction: six-cell supports with pin distribution (3,0) can occur and must be counted. They still have the required small pressure.

Put a same-slope parity wall at zero, and fix every column in [-R,R] to its matching row in {1,2}, where R=ceil(A h sqrt(log h)). The left and right laws may be constant parity or opposite checkerboard phases. Outside the collar, use their prescribed parity classes restricted to rows at least seven wherever a support can interact with the collar or wall. Farther than the full support span L=O(h²), the usual full alphabets may be retained. All variable alphabets have size h/2+O(1).

The complete fixed collar is valid because every binary word on adjacent rows {1,2} is valid for the parity family. This statement uses the normalized fixed-final-F support language.

## 1. The two-sided four/six pinned table

After normalizing horizontal translations, the same upper bounds as for the one-sided buffer remain valid:

| Support arity | Pins | Count |
|---|---:|---:|
| 4 | 1 | O_epsilon(h^(2+epsilon)) |
| 4 | 2 | O_epsilon(h^(3/2+epsilon)) |
| 6 | 1 | O_epsilon(h^(4+epsilon)) |
| 6 | 2 | O_epsilon(h^(3+epsilon)) |
| 6 | 3 | O_epsilon(h^(2+epsilon)) |
| 6 | 4 | O_epsilon(h^(1+epsilon)) |

There are no four-cell events with three pins or six-cell events with five pins. All-fixed supports are excluded by the validity of the adjacent-row word.

Here are the points requiring a new check.

For a mixed four-support with one pin in each black pair, reflect horizontally so that the side vector from its low pin to its free point is U=(x,y), x>0, y≥5. The analogous diagonal vector is V=(z,v), where z can now have either sign. With pin-row difference delta in {-1,0,1}, the equations in Section 7 of [checkerboard_flip_conic_bound.md](checkerboard_flip_conic_bound.md) remain

    x|y Delta,
    v=y+2Delta−2delta,
    z²=x²−4(Delta−delta)(y+Delta−delta),
    Delta≥−1.

All counting steps use z²; recovering z adds at most two signs. In the large reduced-offset branch, the exceptional leading coefficient A=0 gives x=2Delta. Positivity then forces delta=1 and x=|z|=2, hence Delta=1 and reduced offset X=1, already in the small branch. The zero-discriminant branch remains O(h log h), with both z signs counted. Therefore the O(h^(3/2+epsilon)) bound does not require the pins and free points to have a common horizontal order.

If both pins form the same black pair and both free points are on one side, the old one-sided argument applies. If the free points are on opposite sides, a pinned side has horizontal gap at most 2R and vertical gap at most one, whereas the free diagonal has horizontal gap at least 2R+2. Norm equality is impossible. If the pins form the diagonal, the shared-white midpoint row is at most two, so the free side has vertical gap at most two. Its horizontal gap exceeds 2R. The integer connector then has horizontal coordinate zero when R>h, by perpendicularity. Its vertical coordinate is nonzero, forcing a horizontal free side. The other diagonal is then identical to the common-white diagonal, a degeneracy. Thus no new same-pair branch occurs.

A hidden rectangle with two low pins has only O(h) free row pairs: a low diagonal cannot have two high complementary corners, and a low side makes the high rows differ by at most one. Three pins force a bounded unit-diamond completion, not a high free point. A mixed support with three pins has just one free point, so the old one-sided three-pin exclusion still applies.

For six-supports, one or two pins leave a nontrivial completion-row relation, giving respectively h^4 or h^3 free-row assignments, followed by divisor-many geometries. Three pins in distribution (2,1) give h² assignments as before. In distribution (3,0), the pinned triangle is a unit diamond with common corner at row three. The other three high rows satisfy one nontrivial completion relation, again giving h² assignments and divisor-many geometries. This configuration need not be impossible when the free points can be on both sides of the collar.

Four pins in distribution (2,2) force the free rows to differ by at most two. In distribution (3,1), the common corner is at row three and the two free rows differ by one or two. Both give O(h) row pairs. Five pins have distribution (3,2): the first completion is row three, whereas the second is either below the strip or at least row six. This is impossible.

For fixed rows, each tilted black triple has only divisor-many geometries; a zero row product would make it axis aligned or repeat a black column. These facts establish the table without a one-sided placement assumption.

## 2. New two/three-cell events

New vertical-rival events are absent. A cross-wall pair of free points has horizontal separation greater than 2R>h. A pin/free pair on opposite sides has separation greater than R>h. Two pins have row difference zero or one: difference one cannot have an integral longer hypotenuse, and difference zero cannot give an opposite-parity vertical white pair. Same-side pairs retain the protected phase exclusion.

A new three-black singleton rival must cross the wall with an odd corner split. The isolated end gap of a tilted rectangle is at most h. Therefore it cannot have no pins: any corner crossing from a free exterior point to the other side of the wall would have an isolated gap greater than R. It cannot have two pins either: two distinct-column corners in rows {1,2} confine a tilted rectangle to span O(h), while a cross-wall rectangle with a free exterior point has span greater than R.

Thus every new three-cell event has exactly one pin and two free points. The pin is its lowest corner. If its missing corner were lower, that corner and the pin would both lie in rows {1,2}, again forcing span O(h). The isolated corner cannot be the low black pin: both adjacent high corners on one horizontal side would have positive dot product. The isolated corner is therefore the white completion on the other side of the wall, and the two free black points lie on the same side as the pin.

## 3. Incident triangle mass: both free-corner roles

Reflect to put the free points left of the wall. First fix the lower free point (-X,b), X>R, and the pin (-s,a), a in {1,2}, s≥0. Write e=b−a and d=X−s. The perpendicular short side is j(e/g,d/g), where g=gcd(d,e). Its horizontal coordinate f=j e/g must satisfy

    s<f<X−R.

The second inequality is essential: the upper black corner must also lie outside the collar. Together with s≤R it gives s<X/2 and d≥X/2. Vertical containment gives j≤h g/d, hence s≤2he/X. Summing the possible j over this interval of s gives at most

    C[h² e tau(e)/X²+h sigma(e)/X]

geometries at fixed b. Here the interval gcd sum is bounded by its length times tau(e), plus sigma(e). Summing b and multiplying the two-free-cell probability O(h^−2), using sum e tau(e)=O(h²log h) and sum sigma(e)=O(h²), gives

    C[h²log h/X²+h/X].

For the upper free point (-X,c), put q=c−a and write the white completion as (w,a+v), w≥0. Let u=s+w>0 and t=q−v>0. Orthogonality gives

    vt=u(X+w),  0≤w≤u,  u≤U=h²/X.

Write g=gcd(v,u), v=gz, u=ga. Then z divides d=X+w, and

    aX/h≤z≤h/g,  X≤d≤X+u.

There are at most u/z+1 possible multiples d. Summing z and then g|u bounds the count at fixed u by

    C[u tau(u)log(eU/u)+h sigma_(−1)(u)].

Summing u≤U gives C(U²log h+hU). After multiplication by O(h^−2), this is the same incident bound as for the lower free point.

Since X≥R=A h sqrt(log h), the raw event mass through any free column is at most

    C/A²+C/[A sqrt(log h)].

Choose A sufficiently large. This is smaller than any fixed local-lemma threshold required for events on at most six free variables.

The total triangle mean is O(h log h). Indeed the pin row has only two choices, the number of translations isolating the missing corner is at most the smaller horizontal side projection, and the fixed-row primitive min-span sum is O(h³log h). Multiplication by the two-free-cell probability gives the claim. No extra factor R is needed.

## 4. Consequence for the local lemma and remaining comparison

The pinned four/six table gives local pressure O_epsilon(h^(−1/2+epsilon)). Each normalized geometry has at most O(R) translations with a specified pin in the collar, so their total mean is

    O_epsilon(R h^(−1/2+epsilon))=o(h log²h)

for any fixed epsilon<1/2. The new triangles add O(h log h) total mean and the small incident bound in Section 3. Free-only four/six supports retain incident pressure o(1). Thus the full product-form local lemma with weights 2Pr(E) applies after choosing A large and then h large.

In particular, list all free-only four/six bulk events first. Conditional avoidance of the remaining pinned and new-triangle events costs at most exp[-o(h log²h)]. This statement does not multiply the bulk mean by two: the factor-two weights are used only for the subsequent conditional product bound. The bulk avoidance may be estimated separately at its sharper first-order scale.

Fixing O(R) collar letters costs O(R log h)=o(h log²h) in logarithmic word count. Deleting the first six rows is needed only in the O(L+R) exterior columns that can interact with the collar or wall, costing O(L/h)=O(h). Deleting those rows throughout arbitrarily long halves would instead introduce an unnecessary extensive error.

These estimates validate the proposed two-sided collar event system. The following argument completes its finite-interface comparison for ordinary O/C same-slope walls. It does not assert universal canonical-component dominance.

## 5. Exact finite-interface conditioning

Let the two halves each have length at least L, use the normalized fixed-final-F convention throughout, and write

    J_XY=log Z_XY−log Z_X(left)−log Z_Y(right).

Let W_XY be the canonical four/six crossing mean in the independent full-alphabet product space. Then

    J_XY=−W_XY+o(h log²h)

uniformly in these half lengths and the starting phase. For a pure continuation the corresponding identity is J_XX=−W_XX+o(h log²h).

First, the canonical four/six family has both raw incident pressure and compatible proper-extension pressure o(1), uniformly for these column alphabets. These are the uncolored fixed-cell bounds used in [crossed_codegree_and_avoidance.md](crossed_codegree_and_avoidance.md). Deduplication and deletion of supports containing a smaller four-support matter: they exclude a distinct event whose assignment is wholly contained in a conditioned event.

For any canonical event E and any preceding subfamily S, separate the events of S sharing E's variables from those disjoint from them. E is independent of the latter subfamily. The conditional local-lemma bound, applied after fixing E, bounds the sum of compatible neighboring probabilities by their unconditional-under-E sum times 1+o(1). The union bound and Bayes' identity therefore give

    Pr(E | avoid S)=Pr(E)[1+o(1)],

uniformly. This argument uses only the four/six family at this stage. Listing the internal events first and the crossing events afterward gives the claimed first-order conditional crossing expansion for that family. The wall's additional two/three-cell events can only decrease its count, proving J_XY≤−W_XY+o(h log²h).

For the reverse inequality, first restrict the two independently valid half words to the columns outside [-R,R]. Every resulting outside word has at most h^(2R+1) preimages, so the number of outside words avoiding their own internal events is at least Z_X(left)Z_Y(right)/h^(2R+1). Remove rows1 through6 only in the O(L+R) outside columns that can interact with the collar or wall. Adding the corresponding unary bad-letter events to the internal four/six local lemma shows that this loses at most exp[-O((L+R)/h)]. This is a conditional-avoidance statement, not a claim about a prescribed exterior word.

In the resulting high-row product space, first avoid the outside internal events and then the outside crossing four/six events. Their crossing mean is at most [1+O(1/h)]W_XY: deleting supports only helps, and restricting each of at most six alphabets inflates a remaining probability by 1+O(1/h). The preceding uniform first-order expansion applies to this reduced bulk as well. Now fix the central adjacent-row collar and add all pinned four/six and new triangle events. Sections1–4 give a valid joint local lemma and a total conditional logarithmic cost o(h log²h).

Combining the bounds gives

    J_XY≥−W_XY−O(R log h)−O((L+R)/h)−o(h log²h)
         =−W_XY−o(h log²h).

Together with the upper bound this proves the identity. Comparing it with the pure interface and using the audited six-cell masses yields

    J_O,opposite−J_O,pure ~ (2/17)W_(6,O)>0,
    J_C,opposite−J_C,pure ~ (6/7)W_(6,C)>0.

The logarithms here are normalized by their respective two half partition functions. At odd heights, that normalization retains the different odd/even volume rates; it is not an assertion that an arbitrarily long even domain has no volume penalty relative to an odd domain.

This positive interface comparison is compatible with both phases lying in one canonical component. It neither determines an optimal repeated-wall spacing nor supplies an exit from every competing recurrent state.

## 6. An ordinary-parity wall lattice inside the canonical component

Choose a fixed D≥4 and a domain length n equal to D L up to a bounded period-alignment correction. Since every support has span at most L, it meets at most one of the regularly spaced walls. The joint collar estimates above are uniform in the number of domains: collars are disjoint, the local pressure does not increase, and all total costs add over walls.

For a pure protected block of length n, the finite-volume mean is n mu_X−W_X up to O(mu_X). The established protected avoidance expansion and rate expansion each have error O(n h^(−2+eta)). Thus, for a fixed eta<1,

    log Z_X(n)=n log r_X+W_X+O(h^eta).

Each domain contributes this positive endpoint term, whereas each interface costs W_XY+o(h log²h). The pure-to-wall saving is a positive constant times h log²h by Section5. Therefore the wall-lattice language has logarithmic growth at least

    average(log r_X,log r_Y)+c log²h/h.

The two complementary constant-parity rates differ by O(1) in rate, equivalently O(1/h) in logarithmic rate; the complementary checkerboard rates agree by translation. Their difference is lower order than the displayed gain. Consequently, for ordinary parity, this construction exceeds the best pure-phase rate by at least c' log²h in rate for all sufficiently large h.

To capture this language in the canonical component, leave the first and last wall farther than 2L from the core ends and append the established protected phase buffers and adjacent-row tails. Their pinned supports see only protected end regions and do not interact with the wall collars. Adding these events to the same joint local lemma loses a positive factor depending on h but not on the number of domains. Hence the captured language has the same exponential rate. This proves the stated lower bound for the ordinary-parity canonical component; it is not an upper bound on its entropy or a theorem about optimal wall spacing.

## 7. Extension of the collar estimates to the repaired quadratic anchors

The all-pinned proof in [quadratic_low_anchor_complement_wall.md](quadratic_low_anchor_complement_wall.md) passes independent review. The q anchor uses only rows1,2 and has no three-black tilted rectangle. The repaired q+y anchor uses rows1,2,3; its only such rectangles complete at row5 in two distinct central columns, with the same row color as the selected row1 there. The low-row mixed case split and vertical-pair check exclude the remaining all-pinned collisions. The stated connections of the periodic anchors to the boundary component are valid.

For completeness, the two-sided count proof extends to pins in rows1,2,3 if the interacting free alphabets omit rows1 through29. In the signed-diagonal conic, delta lies in [-2,2] and Delta≥−2. Negative Delta forces X≤2. If A=0, then x=2Delta and

    z²=4delta²−2(x−2delta)(y−2delta).

With y≥27, positivity forces delta>0 and x≤2delta≤4, already in the small-X branch. If N=0, then delta>0 and Y divides delta², leaving only boundedly many Y; g is determined by T and the remaining sum is O(h logh). Thus the two-pin mixed bound is unchanged.

For a three-pin mixed support, a pinned diagonal confines the vertical gap of the free side to at most four. If instead the pins form the side, let u be its vertical gap, |u|≤2, and v≥27 the free diagonal gap. The one-sided order of the sole free point, equal norms, and perpendicularity imply

    v²−u²<4|u|T_y≤4v+16,

which is impossible. Hidden three-pin completions have row at most five. For six-supports, a three-pin completion has bounded row at most five; the (3,0) case still has only two independent free-row variables, four pins leave at most one, and five pins cannot complete to the same row with a free letter at least30. This preserves the table in Section1.

The one-pin triangle load estimates use only a bounded number of fixed low rows and a lowest pin; they are unchanged up to absolute constants. A missing corner lower than the pin would give two bounded low corners and span O(h), excluding interaction with the exterior. The repaired q+y anchor's two low completions lie within bounded distance of the central seam; the horizontal-product argument in its Section7 also excludes a second free rectangle sharing either completion.

Accordingly, the finite-interface identity J_XY=−W_XY+o(h log²h) extends to the quadratic complement walls with these audited anchor alignments. It does not assert every reverse orientation at the same fixed cut: the naive reversed q splice has a run of four row2 letters and is invalid. A wall lattice can keep the good alignment at every interface by choosing domain lengths congruent to two modulo four. The full arithmetic and this alignment qualification are checked in [same_slope_resolution_independent_audit.md](same_slope_resolution_independent_audit.md).
