# Mixed collisions in the one-prime scaffold

9 November 2026. This note continues
`../2026-11-08/general_dominance_quadratic/one_prime_scaffold.md`. It studies the
four-black mixed side/diagonal collisions that remain after the Pythagorean (P)
coloring. Earlier reports and the manuscript are unchanged.

**Summary.**

1. Up to the two free swaps, every double-supported collision has one of three
   cell-type patterns. The all-odd and all-even patterns are impossible for every
   prime `p>10h`.
2. Mixed collisions occur inside a single block for **every** prime. At every
   height `h>=514` there is an explicit one: no choice of prime avoids mixed
   collisions, so a coloring or a change of placement is needed.
3. The same-block collisions form a rational family. Their hypergraph is
   `h^{o(1)}`-degenerate, so `h^{o(1)}` separated layers remove them together
   with P.
4. Two kinds of collision remain open: cross-block collisions of type I and all
   collisions of type II. For each of them, the remaining equations are written
   out exactly. Elementary owner counts give only `h^{1+o(1)}` per column. That
   is the stuck point.

Nothing here gives an `h^{2+o(1)}` scaffold free of all double-supported
obstructions. Singleton completion is not addressed.

## 0. Setting and notation

Fix a prime `10h<p<20h`, with `n_o=ceil(h/2)` and `n_e=floor(h/2)`. The double
`(a,b)` sits in column `X(a,b)=4(a+pb)`. Its odd cell is `(X,2a+1)` and its even
cell is `(X,2b+2)`. Call `a` the position and `b` the block. A slot difference
`Delta s=Delta a+p Delta b` is **short** if `Delta b=0`, so that `|Delta s|<h/2`.
Otherwise it is **long**, with `|Delta s|>=p-h/2>9.5h`.

The lifted slots `a+pb+2kM` with `M=p n_e` preserve all residues modulo `p` and
all block structure inside a layer. A collision with all its black cells in one
layer is a translate of a collision in the unlifted placement. Collisions across
layers do not fit, because the layer gap exceeds `W_h`. So it suffices to color
the unlifted collision hypergraph. Its vertices are the double columns.

**Reduction (known).** Inside the scaffold every double-supported collision has
the following form. There are marked cells `A,B,C,D`, two lattice points `P,Q`,
and rectangles `{A,B,P,Q}` (side `AB`) and `{C,D,P,Q}` (diagonal `CD`). Write

    U=B-A,   V=D-C,   H=A+B-C-D.

Then

    |U|^2=|V|^2,   H.U=0,   H!=0,   V!=+-U,   P=A-H/2,   Q=B-H/2.

All other mechanisms are already excluded: three-black tilted corners, hidden
rectangles, and axis-axis collisions. See the proof of section 3.5 of
`quadratic_arithmetic.md`, which uses only those facts. The case `U_x=0` is
exactly the P law. The colors of `P` and `Q` are irrelevant, because the
symmetric difference is `{A,B,C,D}`.

The four cells are distinct. If `A=C`, the two rectangles share three corners
and coincide. So a hyperedge has 2 to 4 columns.

Two swaps are free. Swapping `A` and `B` sends `U` to `-U` and fixes `H`.
Swapping `C` and `D` sends `V` to `-V` and fixes `H`.

## 1. Type classification

Horizontal coordinates are multiples of 4, so `U_y^2 = V_y^2 (mod 16)`. This
means `U_y` and `V_y` have the same parity. Integrality of `P` requires `H_y` to
be even, so an even number of the four cells are odd cells. After the free
swaps, only these patterns remain:

* **Type I:** `A` odd, `B` even, `C` even, `D` odd. Here `U_y` and `V_y` are odd.
* **Type II:** `{A,B}` both odd and `{C,D}` both even, or the reverse.
* **All-odd** and **all-even.**

**Lemma 1.1.** All-odd and all-even collisions do not occur.

*Proof.* **All-odd.** Write `sigma=alpha+p beta` for the slot difference of `AB`,
and `tau=gamma+p delta` for that of `CD`. Then

    U=(4sigma, 2alpha),   V=(4tau, 2gamma).

Reduce the norm equation modulo `p`. It gives `20(alpha^2-gamma^2)=0`. Since
`|alpha+-gamma|<h<p`, this forces `gamma=eps alpha` with `eps=+-1`.

The norm equation then reads `16(sigma^2-tau^2)=0`, so `sigma=eps' tau`. Reduce
modulo `p` again: `alpha=eps' gamma`. If `alpha!=0`, then `eps'=eps`, and
`V=eps U`. If `alpha=0`, then `gamma=0` and `V=+-U`. Both outcomes are excluded.

**All-even.** Write

    U=(4(alpha+p beta), 2beta),   H=(4(lam+p mu), 2mu),

with `|lam|<h`. Dividing `H.U=0` by 4 gives

    4(lam+p mu)(alpha+p beta) + mu beta = 0.

* If `beta!=0` and `mu!=0`, the first term exceeds `4(9h)^2`, while
  `|mu beta|<h^2`. They can't cancel.
* If `beta!=0` and `mu=0`, then `lam=0`, so `H=0`.
* If `beta=0`, then `(lam+p mu)alpha=0`, so `lam=mu=0` and `H=0`.

QED.

**Lemma 1.2 (one short factor).**

* In type I, `16 | H_y`. Write `H_y=16m`. Then `Delta s_H sigma = -m U_y` with
  `m!=0`, and at least one of `sigma` and `Delta s_H` is short. If `sigma` is
  short, then `C` and `D` lie in one block.
* In type II, the odd pair always lies in two different blocks.

*Proof.* **Type I.** The perpendicularity equation is

    16 Delta s_H sigma + H_y U_y = 0.

Since `U_y` is odd, `16 | H_y`. If `m=0`, then `Delta s_H sigma=0`, which forces
`H=0` or the P case. Two long factors would make the left side larger than
`16(9.5h)^2>2h^2>=|H_y U_y|`.

Now suppose `sigma` is short. The norm equation gives
`16tau^2 <= 16sigma^2 + h^2`, so `|tau|<0.56h`. A long `tau` exceeds `9.5h`, so
`tau` is short.

**Type II.** Take odd `A,B` and even `C,D`. If `A` and `B` are in one block, then
`U=(4alpha, 2alpha)`, and the norm equation becomes `5alpha^2=4tau^2+delta^2`,
where `delta` is the block difference of `CD`. If `delta!=0`, then `tau` is long,
and `4tau^2>5alpha^2`. If `delta=0`, then `5alpha^2=4gamma^2`, which forces
`alpha=0`.

The reversed assignment (even `A,B`, odd `C,D`) is symmetric. Suppose `C` and `D`
are in one block. If `B-A` has a nonzero block difference, its long slot term
dominates. Otherwise `4alpha^2=5gamma^2`. QED.

## 2. Mixed collisions inside one block, for every prime

Fix a block `b`. Inside it, the odd cells `(4a,2a+1)` lie on a line of slope 1/2.
The even cells `(4a,2b+2)` lie on a horizontal line. The modulus plays no role
here.

**Proposition 2.1.** Suppose `h>=514`, `p>10h` is any prime, and `b=144`. The
cells

    A=(X(17,b), 35)    odd,
    B=(X(0,b), 290)    even,
    C=(X(196,b), 290)  even,
    D=(X(241,b), 483)  odd

form a type I mixed collision. Its white pair is

    P=A+(840,224),   Q=B+(840,224).

*Verification.*

* `U=(-68,255)` and `V=(180,193)`, with `|U|^2=|V|^2=69649`.
* `H=(-1680,-448)`, and `H.U = 114240-114240 = 0`.
* `U.(840,224) = 0`.
* The rows of `P` and `Q` are 259 and 514.
* All indices are in range: `n_o>=257` and `n_e>=257`. The second rectangle has
  diagonals `CD` and `PQ` and is tilted.

A short script checked this exactly for `h=514` and `p=5147`, including equality
of the two presentations against all scaffold cells. Translation by `p` per
block makes the identity independent of `p`. QED.

So mixed collisions are intrinsic to the block geometry. In particular they
can't be removed by choosing the prime.

### 2.1 The same-block family is rational

Put all four cells of a type I collision in block `b`, at positions
`a_1` (A), `a_2` (B), `a_3` (C), and `a_4` (D). Set

    sigma=a_2-a_1,   tau=a_4-a_3,   z=a_4-a_1,   u=U_y=2(b-a_1)+1.

Then `V_y=2z-u`, `H_y=-2z`, and `Delta s_H=sigma+tau-2z`. The two equations
become homogeneous quadrics:

    (N)  4(sigma^2-tau^2) = z(z-u),
    (O)  8 sigma(sigma+tau-2z) = z u,

with `u` odd and `z!=0`.

Adding them eliminates `u` and gives the conic

    12sigma^2 + 8sigma tau - 4tau^2 - 16sigma z - z^2 = 0.

This conic is nonsingular, with determinant 320, and has the rational point
`(1,-1,0)`. The lines through that point parametrize every rational point:

    (sigma:tau:z) = (4s^2+t^2 : 12s^2-16st-t^2 : 16t(s-t)).

Equation (O) then fixes `u`. So every same-block type I collision is a rational
multiple of

    v(s,t) = ( t(4s^2+t^2),  t(12s^2-16st-t^2),  16t^2(s-t),  8(4s^2+t^2)(s-2t) )

for coprime `(s,t)` with `t!=0` and `s!=t`.

The gcd `g(s,t)` of the four entries divides 320. To see this, let `q` be an odd
prime dividing `g`. It can't divide `t`, because the last entry is congruent to
`32s^3` modulo `t`. So `q` divides `4s^2+t^2` and `s-t`, which forces `q=5`. Also
`25` can't divide `g`, and a 2-adic check bounds `v_2(g)` by 6. A numerical scan
of `|s|,|t|<=30` found only gcds dividing 160.

Proposition 2.1 is the point `(s,t)=(1,8)`, scaled by `-1/32`. Its primitive
vector is `(-17,45,224,255)`.

**Theorem 2.2.** The hypergraph of same-block type I collisions is
`d_h`-degenerate, with `d_h=h^{o(1)}`.

*Proof.* Let `A` own each collision. Fix an owner column `(a_1,b)`. This fixes
`u`. A collision owned by it is `rho v(s,t)/g` with `rho` determined by
`u_prim=8(4s^2+t^2)(s-2t)/g`, which must divide `u`.

For each divisor `d` of `u` and each `g|320`, set `e=s-2t`. It divides
`N=dg/8`, and `t` solves

    17t^2 + 16et + 4e^2 = N/e,

which has at most two roots. So the column owns at most

    C tau(u) max_{N<=40h} tau(N) = h^{o(1)}

collisions. Every vertex set `Y` spans at most `d|Y|` hyperedges, so some vertex
of `Y` lies in at most `4d` of them. QED.

**Corollary 2.3.** Color greedily in degeneracy order against both the P graph
and this hypergraph. This needs `2D_h + 4d_h + 1 = h^{o(1)}` colors. The lifted
scaffold of width `h^{2+o(1)}` then excludes:

* three-double right angles,
* P,
* all-odd and all-even collisions,
* all same-block mixed collisions.

The other three entries of `v`, which are the linear data of roles `B`, `C`, and
`D`, are binary cubic forms in `(s,t)`:

* Role `B`: `u-2sigma = 2(4s^2+t^2)(4s-9t)`.
* Role `D`: `u-2z = 8(4s^3-8s^2t-3st^2+2t^3)`, which is irreducible over `Q`.
* Role `C`: `u-2z+2tau = 2(16s^3-20s^2t-28st^2+7t^3)`.

Owner `A` is enough, so no Thue bound is needed.

## 3. What remains, and where the method stops

These cases remain:

* **(Ia') Type I, `sigma` short, `C` and `D` in a different block.**
  - Let `Delta=b_A-b_C!=0`, `lam=a_1+a_2-a_3-a_4`, and `u=U_y`. Then
    `(lam+2p Delta) sigma = -m u`. This forces `|sigma|<h/152` and
    `|Delta sigma|<h/140`.
  - The norm equation does not involve `p`:

        2(2sigma-2Delta+16m-lam)(2Delta-16m+lam) = (2Delta-8m-u)(Delta-4m).

* **(Ib) Type I, `sigma` long, `Delta s_H` short.**
  - The norm equation forces `delta=+-beta`. With `Delta s_H` short, either `C` is
    in `A`'s block and `D` in `B`'s, or the other way round.
  - Write `e=tau-sigma`. Eliminating `sigma=-mU_y/lam` gives a relation that does
    not involve `p`:

        (F1)  32 e m U_y - 16 e^2 lam = lam (V_y^2-U_y^2).

  - The prime enters only through

        (F2)  (a_2-a_1) + p(b_2-b_1) = -m U_y/lam.

  - The height-9800 certificate is the polynomial solution `e=lam=1`, `m=-k` of
    (F1). (F2) is the condition `2p+c=kt`. Both identities were checked by hand.

* **(II) Type II.** The odd pair crosses blocks (Lemma 1.2), and one of `sigma`
  and `Delta s_H` is short. The equations have the same shape.

**Stuck point.** In each remaining case, fixing an owner column and two small
parameters, `(lam,e)` or `(Delta,sigma)`, leaves a pair of conics in the last
two unknowns. This gives at most four solutions per parameter pair. But the
parameter pairs number about `h^2/10^4` in case Ib, and `h^{1+o(1)}` in case
Ia' after the divisor step. The available owner bound is therefore
`h^{1+o(1)}` per column.

The `p`-free relation and the `p`-relation together define the integer points
of a cone over the intersection of two quadrics in `P^4`, a degree-4 del Pezzo
surface whose coefficients depend on `p`. Fixing a column fixes one coordinate
and leaves a curve. An `h^{o(1)}` bound needs a count of integer points on that
curve, uniform in `p`, that beats the parameter-pair count.

Two outcomes are possible:

1. The surface contains rational lines meeting the box. Then a single column can
   lie in roughly `h` collisions, and the owner method fails for this placement.
2. It doesn't. Then a proof would need either the surface's arithmetic or an
   additional placement freedom, such as a block-dependent twist of positions,
   that destroys the cross-block relations.

Two cheaper routes fail:

* **Choosing the prime.** Each solution of the `p`-free relation forbids at most
  one prime, but the solutions are too many.
* **Separating interacting blocks by color.** About `h/160` blocks interact,
  which costs width `h^3`.

## 4. Audit notes

Each lemma was rechecked adversarially:

* **Lemma 1.1:** the `alpha=0` and `mu=0` boundary cases.
* **Lemma 1.2:** the claim that a short `sigma` forces a short `tau`, and both
  type II assignments.
* **Section 2.1:** the sign and range conventions, and the claim that the gcd
  divides 320.
* **Theorem 2.2:** coverage of every point on the conic, including `(1:-1:0)` at
  `s=t`.

The rechecks found no gap. Two numerical checks ran, each a single
identity-level check:

* the collision of Proposition 2.1;
* the parametrization identities (N) and (O) for coprime `|s|,|t|<=30`.

## 5. Cross-block collisions: twists, lines, and the counting lemma

This section works out case Ib in full: type I with `sigma` long, and the sign
choice that puts `C` in `A`'s block and `D` in `B`'s block. The same three steps
apply to the other sign of Ib, to case Ia', and to type II. They are not carried
out here.

### 5.1 Admissible twists

The general block-twisted placement puts position `a` of block `j` in slot
`a+p beta_j`. Here `beta_0<beta_1<...` are integers, and block `j` carries the
even row `2pi(j)+2` for a permutation `pi`. The untwisted scaffold has
`beta_j=pi(j)=j`.

**Lemma 5.1.** Suppose that, for all blocks `j` and `j'`,

    |pi(j)-pi(j')| <= 76|beta_j-beta_j'|.

Then three results still hold:

* Theorem 1 of `one_prime_scaffold.md`, so no three marked cells form a tilted
  right angle.
* The P-graph divisor bound, with the same `D_h`.
* The layer lift.

Without the condition, the even-vertex step can fail.

*Proof.*

* **Odd-row vertex.** The argument uses only `s = a (mod p)` and the parity and
  size of the rows. The mixed bracket becomes `8a_2+2pi(j_2)-10a_0+1`, which is
  odd with absolute value less than `10h`.
* **Even-row vertex, two nonhorizontal even legs, or an odd endpoint in another
  block.** The horizontal product is at least `16(p-h/2)^2`, which exceeds `h^2`.
* **Even-row vertex, a nonhorizontal even leg to block `j'`, and an odd endpoint
  in the vertex's own block.** The horizontal product is at least
  `16(p|Delta beta|-h/2)`. The vertical product is at most
  `2|Delta pi|(h-1)`. Since `p>10h`,

      8(p|Delta beta|-h/2) >= 76h|Delta beta| > 76|Delta beta|(h-1),

  so the Lipschitz condition closes the case.
* **P pairs.** These lie inside one block, where the argument is unchanged.

Without the condition, adjacent blocks with `|Delta pi|` of order `h` give a
vertical product of order `h^2`. That exceeds the horizontal bound
`16(p-h/2)`, which is about `160h`. QED.

So the admissible twists are Lipschitz reorderings of the even rows, plus
stretching of the block spacing. Stretching by a factor `G` costs a factor `G`
in width.

**The twist doesn't remove the relation without `p`.** In case Ib, the relation
(F1) involves only rows and positions:

* the row offset `c_0=pi(j_2)-pi(j_1)`,
* `x_1=a_1-pi(j_1)`,
* and `m`, `lam`, `e`.

The twist enters only through the slot relation
`sigma=alpha+p(beta_{j_2}-beta_{j_1})`, which is (F2).

For example, the subfamily `e=lam=1` reduces, for every twist, to

    2c_0x_1 = 16mc_0-32m^2+c_0-2,

so `c_0` divides `32m^2+2`. Condition (F2) then asks for a block pair with the
prescribed `(Delta beta, Delta pi)`.

A twist changes which block pairs realize solutions of (F1). It can't remove the
solution set of (F1), and it gives no way to lower the count per column. In the
untwisted placement, `c_0=Delta j`, and realizing the family reduces to the
single condition `2p+c=kt` of the height-9800 family.

### 5.2 The case Ib surface and all its lines

Fix the owner `A`. This fixes `q=2x_1-1`, which is odd. Take the unknowns
`c_0` (equal to `Delta j` with no twist), `m`, `lam`, `e`, and a homogenizing
variable `w`. Put `L=2(p+1)c_0-16m+lam`. The case Ib equations are

    (N)  2eL + (qw-8m)(c_0-4m) = 0,
    (P)  lam(L-e) + 2m(2c_0-qw) = 0.

Here (P) is `2(lam sigma + m U_y)=0`, and (N) is the norm equation divided by 8.
Together they cut out a degree-4 del Pezzo surface `S` in `P^4`.

The height-9800 family satisfies both equations. It has `c_0=2`, `m=-k`,
`lam=e=1`, `q=4-t`, and `4(p+1)=2kt-16k`. With these values, (N) reduces to
`10+32k+32k^2-2t=0`, which holds because `t=16k^2+16k+5`.

**Classification.** The quadric (N) has rank 4: it is a cone over the forms
`e`, `L`, `qw-8m`, and `c_0-4m`. Every line of `S` therefore lies in a plane of
one of the cone's two rulings:

    (R1) e = k(qw-8m),   c_0-4m = -2kL,
    (R2) e = k(c_0-4m),  qw-8m = -2kL.

Restricting (P) to each plane gives a conic. Its determinant is

    R1:  q^2(4k^2+1)(4k(p-1)-1) / (4k(p+1)+1),
    R2:  4(k^2+1)(4p^2-4kp-5).

Two planes need a separate check: `k=-1/(4(p+1))` in (R1), and `k=infinity` in
(R2). Both were checked directly. The 16 lines split as follows.

* **Eight lines over `Q(i)`,** from `k=+-i/2` and `k=+-i`. A line not defined
  over `Q` contains at most one rational point.
* **Eight rational lines,** two in each of four planes:
  - **(R1), `k=1/(4(p-1))`:** `e=(qw-8m)/(4(p-1))`.
  - **(R1), `k=-1/(4(p+1))`:** `e=-(qw-8m)/(4(p+1))` and `lam=8m(1-p)`. This
    plane contains the line `{lam=m=0}`.
  - **(R2), `k=(4p^2-5)/(4p)`:** `e=(c_0-4m)(4p^2-5)/(4p)`.
  - **(R2), `k=infinity`:** the plane `c_0=4m, L=0`, which contains the lines
    `{c_0=m=lam=0}` and `{c_0=4m, lam=-8(p-1)m, 4(p-1)e=qw-8m}`.

**Lemma 5.2.** No rational line of `S` contains an integral point (`w=1`) in the
box that gives a nondegenerate collision.

*Proof.*

* **Lines where `e` is a fraction.** Here `e` is `+-(q-8m)` divided by
  `4(p-1)` or `4(p+1)`. The numerator is odd, so `e` is never an integer.
* **The (R2) lines at `k=(4p^2-5)/(4p)`.** An integral `e` needs
  `p | c_0-4m`. In the box `|c_0-4m|<p`, so `c_0=4m` and `e=0`. The plane
  equation then needs `(4p^2-5) | 2p(q-8m)`, so `(4p^2-5) | q-8m`. That is
  impossible, because `0<|q-8m|<4p^2-5`.
* **The line `{c_0=m=lam=0}`.** It has `H=(4lam,16m)=0`, so it is degenerate.

QED.

So lines don't force polynomially many collisions through an owner in case Ib,
and a twist isn't mandatory on line grounds. The determinants and the
factorizations of the degenerate conics were checked symbolically. That was an
algebraic identity check, not a search.

### 5.3 Bounds for case Ib

**Two-column hyperedges don't occur.** They would need `A` and `C` in one
column and `B` and `D` in one column. Since `lam+e=2(a_1-a_3)` and
`lam-e=2(a_2-a_4)`, both conditions force `lam=e=0`. Then `m=0` and `H=0`.

**Three-column hyperedges** are exactly the cases `lam=+-e`. These are
hyperplane sections of `S`, which are curves of degree 4.

* By Lemma 5.2, every rational component that carries nondegenerate integral
  points has degree at least 2.
* The Bombieri-Pila bound for integer points on a curve of degree at least 2, in
  a box of side `h`, then gives at most `C_eps h^{1/2+eps}` such hyperedges per
  owner `A`.
* Components that are not defined over `Q` contribute `O(1)` points.

**Four-column hyperedges.**

* Fix the owner, `c_0`, and `lam`. Then (P) is linear in `(m,e)` and (N) is a
  conic, so there are at most two solutions. A common component would be a line
  on `S`, which Lemma 5.2 excludes.
* The relation `lam sigma=-mU_y`, with `|sigma|>=9.5h|c_0|`, gives
  `|lam c_0|<=h/76`.
* So owner `A` owns at most

      2 sum_{|c_0|<=h/76} 2h/(76|c_0|) + O(1) <= (h/19)(1+log h) + O(1).

These are owner bounds for role `A` only. The bounds for roles `B`, `C`, and `D`
aren't proved. After fixing one of those cells, the elimination step gives a
conic in place of a line.

### 5.4 What a counting lemma would give

Let `D_j` be the maximum number of `j`-column cross-block hyperedges through one
column, over all roles.

* **Degeneracy route.** An owned degree of `h^theta` gives width `h^{2+theta}`.
  - Width `h^{2+o(1)}` needs this lemma: *uniformly in `p` and in the owner, the
    affine surface `S`, minus the degenerate locus, has `h^{o(1)}` integral
    points in the box.*
  - `S` is a rational log Calabi-Yau surface. Lemma 5.2 removes its lines, the
    usual source of polynomially many integral points, but the uniform statement
    is still an open-type problem.
  - Bombieri-Pila type bounds for degree-4 surfaces give about
    `h^{5/4+eps}`, which is weaker than the elementary `O(h log h)`.
  - An owned bound of `h^{1/2}` gives only width `h^{5/2}`, no better than the
    identifying set already known.
* **Local lemma route.**
  - Color the P graph and the same-block family by degeneracy, with `h^{o(1)}`
    colors. Color the cross-block hypergraph randomly with `K` colors, and use
    the product coloring.
  - The local lemma needs `D_2/K + D_3/K^2 + D_4/K^3` to be small.
  - With `D_2=0`, `D_3<=h^{1/2+eps}`, and `D_4<=h^{1+o(1)}` in every role, this
    gives `K=h^{1/3+o(1)}` and width `h^{7/3+o(1)}`, better than `h^{5/2}`.
  - The role-`A` bounds in section 5.3 have exactly these exponents.
  - A bound `D_4<=h^{1/2+o(1)}` would give width `h^{13/6+o(1)}`.
  - Only an `h^{o(1)}` bound reaches width `h^{2+o(1)}`.

### 5.5 Status

**Proved:**
- the Lipschitz twist lemma, including the need for its condition;
- that the twist doesn't remove the relation without `p`;
- the complete line classification for case Ib, with no line carrying
  nondegenerate integral points;
- for case Ib, no two-column hyperedges;
- for case Ib, owner-`A` bounds of `h^{1/2+eps}` for three-column hyperedges and
  `O(h log h)` for four-column hyperedges.

**Open:**
- the bounds for roles `B`, `C`, and `D`;
- the other sign of Ib, case Ia', and type II;
- the uniform `h^{o(1)}` integral-point lemma.

**Audit:**
- I rederived the Lipschitz constant from `p>10h`.
- I checked the surface equations against the height-9800 family.
- The ruling argument uses the fact that each line of `S` lies in a plane of each
  rank-4 quadric of the pencil, here (N).
- Lemma 5.2 uses that `q=2x_1-1` is odd and that `|c_0-4m|<p` in the box.
- I rederived the two-column exclusion from the identities for `lam+e` and
  `lam-e`.
