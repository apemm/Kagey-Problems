# Safe triangles and a restricted pair first moment

9 November 2026. This note refines the placement step for the fully
filled period-seven profiles. It retains certain three-black tilted
rectangles whose singleton completions are harmless. The remaining
two-label geometries have a weighted first moment with logarithmic
exponent two. The resulting threshold is
\[
m_0(h)\ll_\varepsilon h^2(1+\log h)^{2+\varepsilon}.
\tag{1}
\]
The proof has passed independent review, including the complete pair
role list and the restored six-cell events. See
[safe_triangle_first_moment_independent_audit.md](safe_triangle_first_moment_independent_audit.md).
The earlier fourth-logarithm theorem remains a separate established
result.

## 1. Orient and separate the profiles

Use the profiles and exceptional set in
[filled_mod7_profile_cover.md](filled_mod7_profile_cover.md).
Write \(S=\{L,F,H\}\), with \(L,F=O(1)\),
\(H=h-O(1)\), and normalized residues \(0,3,1\), respectively.
Choose \(L\) odd, hence \(F\) odd and \(H\) even.

For a parity label whose odd endpoint is \(a\) and even endpoint is
\(b\), choose the unique odd \(L\in[1,14]\) congruent to \(a\)
modulo seven. If \(a\not\equiv b\pmod7\), choose
\(g=(b-a)/5\pmod7\). Assign the label to a **mixed-residue block**
of this profile. Its odd endpoint has normalized residue zero and its
even endpoint has normalized residue five. If the two residues agree,
choose any nonzero \(g\), and assign the label to a separate
**zero-residue block**. Both endpoints then have normalized residue
zero. No block mixes these two types. This changes the number of
profile families by only an absolute constant.

Enlarge the exceptional row set by the finitely many identities
\[
r=s+t-u,\qquad s,t,u\in S,
\tag{2}
\]
for every profile. There are only an absolute constant number of such
rows. The exceptional-label cost remains \(O(h^2)\). All ordinary
label rows remain in \([5000,h-5000]\).

Two simple consequences will remove possible coincident arithmetic
factors. If \(a,b\) are the endpoints of an ordinary label and
\(s,t\in S\), then
\[
a-b\ne s-t,\qquad a+b\ne s+t.
\tag{3}
\]
For the first identity, a low/low sea difference is even, whereas
\(a-b\) is odd. A high/low difference is larger in absolute value
than any difference between two bulk rows. For the second identity,
mixed-residue labels have normalized row sum five, whereas the possible
sea sums are \(0,1,2,3,4,6\). A zero-residue label could only match
the sea sum \(L+L\), but its physical row sum is odd and \(2L\)
is even.

## 2. Which three-black triangles can be retained

Continue to forbid every three-black tilted rectangle except a right
angle rooted at a high sea point, with its other two black corners in
two distinct labels of a mixed-residue block. Call these **allowed
triangles**. They use one odd endpoint of normalized residue zero and
one even endpoint of normalized residue five.

This is exactly the list of possible sea-rooted right angles. All
label columns are zero modulo seven. At a low sea point, the modular
right-angle equation for endpoint residues \(r,s\in\{0,5\}\) is
\(x^2+rs=0\), with \(x\ne0\). It has no solution: the products
are zero or four, and \(-4=3\) is a nonsquare. At a filler point,
the two horizontal differences vanish modulo seven and
\((r-3)(s-3)\ne0\). At a high point the equation is
\[
x^2+(r-1)(s-1)=0.
\]
The equal-residue choices require a nonsquare value of \(x^2\).
The mixed choice requires \(x^2=4\). Since a high sea column is a
nonzero square, it has normalized column residue two. These statements
also show that zero-residue blocks have no sea-rooted triangles.

Let the high corner be \(X\), and the label corners be \(A,B\).
The fourth corner is \(W=A+B-X\). It has normalized column residue
five and row residue four. Thus its column is a low sea column but
its row is not \(L\): it is always white. Its physical row parity is
\[
W_y\equiv\text{odd}+\text{even}-\text{even}
\equiv L\pmod2.
\tag{4}
\]
Therefore its singleton presentation has no axis rival from the final
parity graph. The remaining black point in its column is the low sea
point, with the same parity as \(W\). There is no hidden rectangle
containing an allowed triangle, because its completion is white.

Two distinct allowed triangles using only the same two labels cannot
have the same white completion. Their label-column sum is the same,
so equality of the completion column forces the same high sea corner
\(X\). If the two choices of label rows are \((a,d)\) and
\((b,c)\), equality of the completion rows and the right-angle
equations give
\[
a+d=b+c,\qquad
(a-H)(d-H)=(b-H)(c-H).
\]
Hence the two unordered row pairs agree. Since the endpoints within
each label are distinct, either the triangles agree or the two labels
are the same unordered edge. Distinct labels exclude the latter case.

All other singleton collisions between allowed triangles have either
a common black corner, hence a four-cell symmetric difference, or six
distinct black corners. The four-cell cases are already forbidden by
the ordinary four-support classification. The genuine six-cell cases
use three or four labels and are included separately in Section 6.

This list is complete. Every other tilted three-black rectangle remains
forbidden. A hidden tilted rectangle would contain such a forbidden
triangle, since an allowed triangle always completes at a white cell.
Axis hidden rectangles are excluded by distinct parity labels.
The usual four-support and singleton-presentation classification then
accounts for every remaining collision.

## 3. A weighted divisor estimate

Put
\[
Q=\lfloor h^2/4\rfloor,\quad
\Lambda=1+\log h,\quad \ell=1+\log\log(3h),
\qquad
v(e)=1+\sum_{r\in e,\ s\in S}\tau(|r-s|).
\tag{5}
\]
For each fixed positive \(s\) in a compact interval containing one,
write \(\beta(s)=2^s-1\). The single-form divisor moment gives
\[
\sum_e v(e)^s\ll_s Q\Lambda^{\beta(s)}.
\tag{6}
\]

The weighted estimates needed below are the following. For distinct
primitive bounded-coefficient affine forms in one variable, with
constant terms \(O(h)\),
\[
\begin{aligned}
\sum_{t\le h}\tau(C(t))^s\tau(A(t)^2)
 &\ll_s h\Lambda^{\beta(s)+2}\ell^{C_s},\\
\sum_{t\le h}\tau(C(t))^s\tau(A(t))\tau(B(t))
 &\ll_s h\Lambda^{\beta(s)+2}\ell^{C_s},\\
\sum_{t\le h}\tau(C(t))^s\tau(A(t))
 &\ll_s h\Lambda^{\beta(s)+1}\ell^{C_s}.
\end{aligned}
\tag{7}
\]
Absolute values are understood, and zero arguments are removed.
The first estimate requires \(A,C\) distinct. The second requires
all three factors distinct. Bounded contents cost only a constant.

These are the multivariate-arithmetic-function specialization of
[Henriot, Corollary 2](https://arxiv.org/pdf/1102.1643), with the
[2014 erratum](https://doi.org/10.1017/S0305004114000280).
Apply it to the distinct primitive factors, with arithmetic function
\(\tau(n_1)^s\tau(n_2^2)\), or
\(\tau(n_1)^s\tau(n_2)\tau(n_3)\). The ordinary-prime coefficients
are \(\beta(s)+2\), or \(\beta(s)+1\) for the last estimate.
The corrected exceptional primes divide the bounded leading
coefficients and the nonzero resultants. Their product has size
\(h^{O(1)}\), so its Euler factor is \(O_s(\ell^{C_s})\).
Translate the interval to \([h,2h]\). Polynomial height is at most
\(O(h^3)\), so a fixed size parameter such as \(1/4\) suffices.
The divisor functions satisfy the required submultiplicativity and
subpower growth. Thus the constants in (7) are uniform in the shifts.
This uses only the upper bound, which survives the erratum.

The corresponding two-variable estimates follow by conditioning on
one variable. If a root coincidence occurs only at finitely many
values of the conditioned variable, remove those slices. Each slice
contains \(O(h)\) labels, and the uniform maximum-divisor bound makes
its total \(h^{1+o(1)}\). If the class-weight factor uses only the
conditioned variable, apply the unweighted first moment in the other
variable, then apply (6) in the conditioned variable. For a single
geometric factor depending on both variables, average the variable
not used by the class-weight factor first.

Fix a nonempty dyadic class
\(\mathcal C_w=\{f:w/2<v(f)\le w\}\), of size \(n\), and
let \(e\in\mathcal C_w\). For any fixed small \(d>0\), define
\[
M(w)=\min\left\{1,
C_d\frac{\Lambda^{\beta(1-d)}}{w^{1-d}},
C_d\frac{\Lambda}{w},
C_d\frac{\Lambda^{\beta(1+d)}}{w^{1+d}}\right\}.
\tag{8}
\]
In particular, \(n\ll Q M(w)\).
For each of the three exponents in (8), class membership is bounded
by a constant times
\[
w^{-s}\sum_{r\in f,\ t\in S}\tau(|r-t|)^s.
\tag{9}
\]
The additive one in (5) is harmless because there are six positive
divisor terms. Estimate (9), or the trivial bound one, will produce
the minimum in (8).

## 4. The restricted pair lemma

Let \(G_{e,f}\) count relative translated geometries involving
exactly the two labels \(e,f\) of the following forbidden supports:
three-black tilted rectangles other than the allowed triangles,
mixed four-cell supports, and vertical parity rivals. Sea points must
belong to the fixed profile. Then, uniformly in \(e\in\mathcal C_w\),
\[
\boxed{
\sum_{f\in\mathcal C_w\setminus\{e\}}G_{e,f}
\ll_d Q\ell^{C_d}(\Lambda^2+w\Lambda)M(w)
       +h^{1+o(1)}.}
\tag{10}
\]
The subpower term is uniform in the fixed label and profile.
There are only constantly many roles and endpoint choices, so it
suffices to verify one assignment at a time.

### Three-black triangles

With one point from each label and one sea point, an angle rooted at
a label point has a horizontal product equal to
\((c-a)(s-a)\), or \((a-c)(s-c)\). Here \(a\in e\),
\(c\in f\), and \(s\in S\). One factor is private to a label,
and its divisor function is at most \(w\). The remaining factor
\(c-a\) has a root at a bulk row, distinct from every class-weight
root \(c-t\), \(t\in S\). The last estimate in (7), and an
independent sum over the unused endpoint of \(f\), give the
\(Qw\Lambda M(w)\) term. Angles rooted at sea points are precisely
the allowed triangles from Section 2, so they create no forbidden
two-label event.

With two black points from one label and one from the other, a tilted
right angle can only be at the lone point. The relative column gap
then has one prescribed square, hence at most two values. These roles
contribute \(O(n)\), absorbed by (10).

### Vertical rivals and horizontal mixed sides

A vertical rival from endpoints \(a\in e,c\in f\) has
\(O(\tau((c-a)^2))\) relative geometries. Equal-row diagonals are
parity-safe. The nonzero difference has a bulk root, distinct from the
private class-weight roots. The first estimate in (7) gives
\(Q\Lambda^2\ell^{C_d}M(w)\).

For a horizontal mixed side, the corresponding count is the divisor
function of the black diagonal's squared row difference. If the side
consists of two sea points, its label diagonal uses one endpoint of
each label, giving the same estimate. A side joining a label and sea
point is impossible because label rows are bulk rows. If both side
endpoints are labels, they have the same row. For fixed \(e\), this
leaves only \(O(h)\) possible \(f\)'s, contributing
\(h^{1+o(1)}\). A diagonal consisting of the two endpoints of one
label has odd row sum and cannot give an integral horizontal pair.

A fixed label cannot supply both a diagonal endpoint and a horizontal
side endpoint. For a diagonal with nonzero vertical difference and
the same length as the side, its endpoint columns lie strictly
between the two side endpoint columns. A diagonal using two sea levels
has either odd row sum, or the bounded difference \(F-L\).
The latter is again absorbed by the equal-row slice bound.

### Nonhorizontal mixed sides

For black side \(A,B\) and black diagonal \(C,D\), put
\[
y=B_y-A_y,\qquad z=C_y+D_y-A_y-B_y.
\]
When the side is nonhorizontal and nonvertical, the number of relative
geometries is \(O(\tau(|yz|))\). The side's horizontal component
divides \(yz\), and the remaining horizontal differences are then
determined up to a bounded number of signs. Both \(y,z\) are nonzero
in a nondegenerate role. A vertical black side is an axis rival and
is already covered by the vertical-pair classification.

Here is the complete role list. Write \(e=\{a,b\}\),
\(f=\{c,d\}\), and let \(s,t\in S\). Signs of factors do not
affect the count.

| Black side | Black diagonal | Product factors | Estimate |
| --- | --- | --- | --- |
| \(a,c\) | \(s,t\) | \(c-a,\ c+a-s-t\) | two distinct nonprivate factors |
| \(a,c\) | \(b,s\) | \(c-a,\ c+a-b-s\) | two distinct nonprivate factors |
| \(a,c\) | \(d,s\) | \(c-a,\ c+a-d-s\) | two varying factors, with finitely many exceptional \(d\)-slices |
| \(a,c\) | \(b,d\) | four points in two double columns | impossible for distinct labels |
| \(a,s\) | \(c,t\) | \(s-a,\ a+s-c-t\) | one private factor, one nonprivate factor |
| \(a,s\) | \(c,d\) | \(s-a,\ a+s-c-d\) | one private factor, one two-variable factor |
| \(a,s\) | \(b,c\) | \(s-a,\ a+s-b-c\) | one private factor, one nonprivate factor |
| \(c,s\) | \(a,t\) | \(s-c,\ c+s-a-t\) | one private factor, one nonprivate factor |
| \(c,s\) | \(a,b\) | \(s-c,\ c+s-a-b\) | one private factor, one nonprivate factor |
| \(c,s\) | \(a,d\) | \(s-c,\ c+s-a-d\) | one private factor, one two-variable factor |
| \(s,t\) | \(a,c\) | \(t-s,\ s+t-a-c\) | bounded low/low factor, or a codimension-one high/low role |

Rows using another endpoint of a label are obtained by relabeling.
A repeated occurrence of the same endpoint would repeat the same
physical black cell, so it is not a four-distinct-cell support.

For completeness, the root-coincidence checks in this table are as
follows.

1. In the first row, the two factors could agree only if
   \(2a=s+t\). A high/low sum is odd, and a low/low average is
   below the bulk. The high/high average is \(H\). All cases are
   excluded. The second factor could be private to \(f\) only if
   \(a=s+t-u\), which was removed in (2).

2. In the second row, a private second factor would require
   \(b-a=u-s\), excluded by (3). The factors could agree only if
   \(2a=b+s\), but that identity permits no genuine mixed support.
   To see this, place the side at \((0,a),(x,c)\) and the diagonal
   at \((0,b),(z,s)\), and put \(y=c-a\ne0\).
   Perpendicularity and equal norms give
   \[
   x(z-x)=y^2,\qquad x^2+y^2=z^2+(s-b)^2.
   \]
   Hence \(xz=x^2+y^2>0\) but
   \(z(z-x)=-(s-b)^2\le0\). The first equation forces \(x,z\),
   and \(z-x\) to have the same sign, a contradiction.

3. In the third row, condition on \(d\). The geometric roots
   coincide only at \(d=2a-s\). A geometric root coincides with a
   private root \(c-u\) only at \(d=a+u-s\). Remove these finitely
   many slices, each containing \(O(h)\) labels. For a class-weight
   factor on \(c\), apply (7) to the three distinct factors. For
   a weight on \(d\), average the two geometric factors over
   \(c\) first and then apply its single-form weight moment.

4. The fourth row is impossible. The center difference of the two
   pairs is vertical, so perpendicularity gives
   \((c-a)(b+d-a-c)=0\). Equal norms give
   \((c-a)^2=(d-b)^2\). If \(c=a\), the labels coincide.
   Otherwise these equations force either \(b=a\), repeating a
   black point, or \(b=c,d=a\), repeating the unordered label.

5. In each remaining ordinary row, remove the private divisor factor
   by the bound \(w\). A remaining one-variable factor can be
   private only through (2), a difference identity in (3), or the
   sum identity in (3). All are excluded. A remaining two-variable
   factor is averaged first in the variable not used by the weight
   from (9). These give the \(Qw\Lambda M(w)\) term.

6. For the final row, \(t-s=F-L\) is bounded when both sea levels
   are low. Its remaining root is nonprivate by (2), so its first
   moment is no larger than (10). For a high/low side, its vertical
   span is \(h-O(1)\). The perpendicular translate has only
   \(O(1)\) possible integer vertical components \(j\), and the
   diagonal row sum is \(s+t+2j\). Fixing the endpoint of \(e\)
   fixes one endpoint of \(f\), leaving \(O(h)\) labels. Uniform
   subpower divisor bounds give \(h^{1+o(1)}\).

Apply (7) and (9) to these rows, and also apply their unweighted
versions. Taking the minimum over these estimates proves (10).
No private-private product remains: the only such ordinary
three-corner role was an angle at a sea point, and Section 2 retained
exactly the geometrically possible instances of that role.

## 5. Summing the pair contribution

The density bound \(M(w)\le\min(1,C\Lambda/w)\) gives
\[
\sum_j M(w_j)\ll 1+\log\Lambda.
\tag{11}
\]
Using the bounds at \(1-d\) and \(1+d\), sum the two geometric
tails of \(w_jM(w_j)\) around their crossing point. This gives
\[
\sum_j w_jM(w_j)
\ll_d
\Lambda^{[\beta(1-d)+\beta(1+d)]/2}
=\Lambda^{2\cosh(d\log2)-1}.
\tag{12}
\]
The exponent tends to one as \(d\downarrow0\). Therefore, for
every \(\varepsilon>0\), the sum of the right side of (10) over
all nonempty classes is
\[
\ll_\varepsilon Q\Lambda^{2+\varepsilon}.
\tag{13}
\]
The \(O(\log h)\) uniform subpower remainders contribute only
\(h^{1+o(1)}\), and every fixed power of \(\ell\) is absorbed by
\(\Lambda^\varepsilon\).

## 6. Higher arity and the restored six-cell events

For the remaining original forbidden supports on \(k=3,4\) labels,
the established squared geometry bound in
[compatible_profile_threshold.md](compatible_profile_threshold.md)
still applies. Removing some triangles only decreases those counts.
For a class of size \(n\) and upper weight \(w\), it gives
\[
\sum_{\substack{J\ni e,\ J\subseteq\mathcal C_w\\|J|=k}}G_J
\ll (nQ)^{(k-1)/2}A(w),\qquad
A(w)=\Lambda^4\ell^C+w\Lambda^{3/2}.
\tag{14}
\]

Now restore the genuine six-cell collisions of allowed triangles.
Each uses two high sea corners and four label points. For a fixed
row-role assignment, their common completion requires
\[
r_1+r_2=r_3+r_4.
\tag{15}
\]
The four label cells are distinct. With \(k=3\) or four labels and
one label fixed, (15) is a nontrivial equation in at least one free
endpoint, so there are \(O(Q^{k-1}/h)\) row assignments.
For each assignment, a high-root triangle's two horizontal legs have
product \(-(r-H)(s-H)\). The two factorization counts are uniformly
\(h^{o(1)}\). Aligning their white completions fixes all relative
columns. Hence their squared geometry count summed over all other
labels is
\[
O\bigl(Q^{k-1}h^{-1+o(1)}\bigr).
\tag{16}
\]
Cauchy--Schwarz restricted to the class gives incident count at most
\((nQ)^{(k-1)/2}h^{-1/2+o(1)}\), absorbed in (14).
There is no genuine two-label six-cell event by Section 2.

## 7. Placement and the total width

Choose each center independently from \(N\) designated period-zero
slots. Let \(B(w)\) denote the right side of (10), enlarged by a
fixed constant. Choose
\[
N=\left\lceil C_0\left(
B(w)+\sqrt{nQ}\sqrt{A(w)}+n+1\right)\right\rceil.
\tag{17}
\]
Every translated geometry using \(k\) centers has probability at
most \(N^{-(k-1)}\). The pair contribution is controlled by
\(B(w)/N\). For \(k=3\), (14) is controlled by
\(nQ A(w)/N^2\). For \(k=4\), it is controlled by
\((nQ)^{3/2}A(w)/N^3\), since \(A(w)\ge1\).
The term \(n\) handles coincident centers. For sufficiently large
absolute \(C_0\), the product-form local lemma therefore gives a
placement avoiding all the forbidden events. Every event uses at
most four center variables, including the restored six-cell events.
The geometric completeness argument in Section 2 gives a valid
fully filled block.

To sum the higher-arity term, use
\[
\sqrt{A(w)}\ll\Lambda^2\ell^C+\sqrt w\Lambda^{3/4}.
\]
The established first-moment class estimate gives
\(\sum_j\sqrt{n_j}\ll\sqrt{Q(1+\log\Lambda)}\).
Also, by Cauchy--Schwarz over the \(O(\log h)\) classes and (6)
at \(s=1\),
\[
\sum_j\sqrt{w_jn_j}
\ll\sqrt{\log h\sum_jw_jn_j}
\ll\sqrt Q\,\Lambda.
\]
Thus
\[
\sum_j\sqrt{n_jQ}\sqrt{A(w_j)}
\ll Q\left(
\Lambda^2\ell^C\sqrt{1+\log\Lambda}+\Lambda^{7/4}
\right)
\ll_\varepsilon Q\Lambda^{2+\varepsilon}.
\tag{18}
\]
Together, (13), (17), and (18) give the same bound for all internal
class widths. There are only an absolute constant number of profiles.
The \(O(\log h)\) classes need \(O(h^2\log h)\) filled collars,
and the exceptional labels cost \(O(h^2)\). Constant tails give
every larger width, proving (1).

The profile argument applies for all sufficiently large heights.
The earlier all-height construction handles the finitely many smaller
heights, which are absorbed by enlarging the constant in (1).

The remaining logarithmic loss is in the averaged arithmetic of
multi-label supports. This argument does not establish an absolute
quadratic threshold.
