# Classification of full row-class boxes with arbitrary column phases

9 November 2026. A vertical-rival dichotomy removes the column-period assumption. The complete proof and the width-nine strengthening passed [independent review](full_box_local_classification_audit.md). This classifies the boxes that avoid singleton-axis and vertical-pair axis rivals. It does not assert that all assignments in these boxes are valid seas; four- and six-cell collisions remain.

Let \(h\ge8\), let \(c:[1,h]\to\mathbb F_2\) define a balanced row partition, and let \(t:\mathbb Z\to\mathbb F_2\) be arbitrary. At column x, allow every row in
\[
 B_{t_x}=\{y:c(y)=t_x\}.
\tag{1}
\]
Use the complete pair set between \(B_0\) and \(B_1\) for axis rivals.

**Theorem.** The box (1) avoids every singleton-axis and vertical-pair axis rival if and only if
\[
 \begin{aligned}
 c(y)&=\kappa q(y)+\alpha y+\beta,\\
 t_x&=\kappa q(x)+\gamma x+\delta,
 \end{aligned}
 \qquad q(n)=n(n-1)/2\bmod2.
\tag{2}
\]
Balance requires ordinary parity when \(\kappa=0\). When \(\kappa=1\), \(q(y)\) is always balanced, while \(q(y)+y\) is excluded if \(h\equiv2\pmod4\).

The same infinite-strip theorem holds at height six. Height seven has an explicit nonquadratic exception, given in Section 5.

For \(h\ge8\), and also for \(h=6\), a finite column interval of width nine already suffices: if its full row-class box avoids these two types of rival, then c has (2), and t has the stated polynomial form on the whole interval. Every required forbidden support has horizontal span at most four.

## 1. Vertical rivals force a complementary translate

For \(s\in\{0,1\}\), define
\[
 D_s=\{k\ge1:\text{ some }a\in B_s
      \text{ has }a-k,a+k\in[1,h]
      \text{ and }c(a-k)\ne c(a+k)\}.
\tag{3}
\]
Every \(k\in D_s\) forbids
\[
 t_x=t_{x+2k}=s.
\tag{4}
\]
Indeed the black cells \((x,a),(x+2k,a)\) are a horizontal diagonal of a tilted square whose vertical diagonal has rows \(a-k,a+k\). The latter is a cross-class pair. The midpoint column has another available row in its prescribed class, so both displayed cells can be made white. Equivalently, the standard positive vertical-rival support already gives (4).

Suppose both \(D_0,D_1\) are nonempty. Choose \(k_0\in D_0,k_1\in D_1\), and put
\[
 a=2k_0,\qquad b=2k_1,\qquad P=a+b.
\]
Thus equal zeros are forbidden at distance a, and equal ones at distance b. If \(t_x=0\), the two implications
\[
 t_{x+a}=1,\qquad t_{x+a+b}=0
\]
give \(t_{x+P}=t_x\). Starting from \(t_x=1\), first use distance b and then distance a to get the same conclusion. Therefore t has period P.

Period P turns the no-equal-ones condition at distance b into the same condition at distance a. Together with the no-equal-zeros condition, this gives
\[
 t_{x+a}=1-t_x
\tag{5}
\]
for every x.

Horizontal translation by a therefore turns the allowed full box into its complementary box. Both boxes avoid singleton rivals. If a rectangle with four distinct corner columns had odd XOR of the cell values \(c(y)+t_x\), exactly three corners would be allowed in one of these two boxes. That realizable three-black support would have a singleton-axis rival. Consequently
\[
 \bigoplus_{\text{rectangle corners }(x,y)}(t_x+c(y))=0
\tag{6}
\]
for every rectangle with four distinct corner columns.

## 2. Four-column templates identify both functions

For completeness, only two rectangle templates are needed to extract (2) from (6). Their adjacent side vectors are
\[
 (1,2),(2,-1),\qquad (1,3),(3,-1).
\]
Write \(d_x=t_x+t_{x+1}\). Their horizontal corner sets give
\[
 d_x+d_{x+2}=\kappa_2,\qquad
 d_x+d_{x+3}=\kappa_3,
\tag{7}
\]
where the respective row expressions show that each right side is independent of x.

Compare the first relation at \(x+1\) with the second at x:
\[
 d_{x+1}+d_x=\kappa_2+\kappa_3.
\]
Iterating this equality twice, then using the first relation in (7), forces \(\kappa_2=0\). Hence successive d-values differ by \(\kappa_3\), and
\[
 t_x=\kappa_3q(x)+\gamma x+\delta.
\]

Now put \(e_y=c(y)+c(y+1)\). The same templates give
\[
 e_y+e_{y+2}=0\quad(1\le y\le h-3),\qquad
 e_y+e_{y+3}=\kappa_3\quad(1\le y\le h-4).
\]
The first makes e two-periodic. The second has an instance when \(h\ge5\), and fixes the difference between its two parity values. Therefore
\[
 c(y)=\kappa_3q(y)+\alpha y+\beta,
\]
with the same quadratic coefficient.

## 3. An empty symmetry-defect set forces ordinary parity

Suppose instead \(D_s=\varnothing\) for some s. Every \(a\in B_s\) is a reflection center of c wherever both reflected rows lie in the strip. In particular,
\[
 a,b\in B_s,\quad 2a-b\in[1,h]
 \quad\Longrightarrow\quad 2a-b\in B_s.
\tag{8}
\]
A nonempty set with (8) is a full residue class in the strip. To see this, take its smallest positive pair difference d. A pair attaining d propagates under reflection to the entire corresponding residue class. Any additional point outside that class would be at distance less than d from a propagated point, including in either boundary tail. This contradicts minimality. Singletons are included by taking a sufficiently large modulus.

Balance gives
\[
 |B_s|\ge\lfloor h/2\rfloor>\lceil h/3\rceil
\tag{9}
\]
when \(h\ge8\), and also when \(h=6\). A proper residue class with modulus at least three cannot satisfy (9). Modulus one would be the whole strip. Thus \(B_s\) is one whole ordinary parity class, and the other block is its complement.

For ordinary row parity, each of the two templates in Section 2 can be vertically translated by one while remaining in the strip when \(h\ge6\). This complements all four row colors. If the four corresponding t-values had odd XOR, one of the two vertical placements would have exactly three allowed corners and give a singleton rival. Hence both template XORs vanish. Equation (7), now with zero row sums, forces \(t_x=\gamma x+\delta\). This proves necessity in the empty-\(D_s\) case.

## 4. Sufficiency and the finite-window statement

For a rectangle with perpendicular adjacent vectors \(u,v\), the four-corner XOR of the expression in (2) is
\[
 \kappa(u_xv_x+u_yv_y)=\kappa(u\cdot v)=0.
\]
Three allowed black corners therefore force the fourth corner to have the same prescribed row class as its column's black letter. There is no singleton-axis rival.

If a tilted rectangle displays a vertical pair and its other two corners are allowed black cells, the same XOR identity makes the two displayed cells' row colors equal, because their column contributions cancel. They cannot form a cross-class vertical rival. This proves sufficiency.

The short-step refinement is as follows. For any proper balanced block \(B_s\), if \(1\notin D_s\), then \(B_s\) has no adjacent pair: such a pair propagates by reflection at distance one to the whole strip. If also \(2\notin D_s\), then a gap-two pair propagates a full parity class, and no additional row can coexist with it without creating an adjacent pair. Otherwise \(B_s\) is three-separated and has at most \(\lceil h/3\rceil\) rows, contrary to (9).

Thus, if the partition is not ordinary parity, each color has a witness \(k_s\in D_s\cap\{1,2\}\). At least one color has \(1\in D_s\). Otherwise neither color has adjacent members, which itself forces ordinary row parity.

Suppose only one color has \(1\in D_s\). The other then has \(2\in D_s\). On either parity of the column indices, these constraints forbid equal ones at distance one and equal zeros at distance two, after exchanging the color labels if needed. No five-bit word satisfies these two rules. If its middle bit is one, its two neighbors must be zero, violating the distance-two rule. If the middle bit is zero, both endpoints must be one; those endpoints force the two neighbors of the middle to be zero, giving the same violation.

Nine consecutive columns contain five columns of one parity. Hence this mixed-step case is impossible on a window of width nine.

It follows that a nonordinary partition must have
\[
 1\in D_0\cap D_1.
\]
Its phase therefore obeys
\[
 t_{x+2}=1-t_x
\tag{10}
\]
wherever both columns lie in the window. This already gives
\(t_x=q(x)+\gamma x+\delta\) on the whole window.

The two-column translate of either template in Section 2 fits alongside the original in a seven-column interval. Equation (10) supplies complementary contexts for every vertical placement. Thus both templates have even cell XOR. Since the phase is now known, the row identities are
\[
 e_y+e_{y+2}=0,\qquad e_y+e_{y+3}=1
\]
on their full row ranges. They force \(c(y)=q(y)+\alpha y+\beta\), as in Section 2.

If the row partition is ordinary parity, Section 3 directly gives the two zero-XOR template recurrences for t. Five consecutive columns suffice to force an affine t. This completes the finite-width-nine proof for every \(h\ge8\) and for \(h=6\). All vertical supports used have span two or four, and the two singleton templates have span three or four.

## 5. The height-seven exception and the scope of the result

At height seven, let
\[
 B_1=\{1,4,7\},\qquad B_0=\{2,3,5,6\},\qquad t_x=1.
\tag{11}
\]
This is a balanced nonordinary, nonquadratic row partition. Its constant full box has no singleton-axis rival: the black rows form a residue class modulo three, and the fourth-corner row \(a+c-b\) remains in that class.

For a vertical rival using two different black rows, one endpoint is row 1 or row 7. A longer vertical diagonal with the same midpoint must leave the strip. For equal black rows, the vertical displayed rows are symmetric around a member of \(B_1\); they are either both 1 modulo three or both outside that residue class. Thus no vertical cross-class pair occurs.

Example (11) proves that the theorem's exclusion of height seven is necessary. It is not a valid full sea shift: other mixed four-cell supports can still occur. The classification concerns exactly the two rival families in its hypothesis.

The small Boolean calculation in [row_class_phase_sft.py](row_class_phase_sft.py) independently found exactly the ordinary and quadratic partition orbits at heights eight through twelve. It imposes these two rival families only. All graphs were completed, and even retaining only forbidden supports of horizontal span at most four gave the same answer. An independent equal-diagonal rectangle generator checked all 2,048 combinations of a six-row coloring and a five-column phase word against the compiled clauses; see [row_phase_projection_independent_check.json](row_phase_projection_independent_check.json). The analytical proof above does not depend on that enumeration.

## 6. A quantitative dichotomy for alphabets with omissions

The vertical-rival step has a robust version even when the row alphabets vary arbitrarily. Suppose
\[
 A_x\subseteq B_{t_x},\qquad |B_{t_x}\setminus A_x|\le M
\]
at every column, and every alphabet has at least two rows. For each s and k, let
\[
 n_s(k)=\#\{a\in B_s:a\pm k\in[1,h],\
                         c(a-k)\ne c(a+k)\}.
\]
If \(n_s(k)>2M\), two columns at distance \(2k\) cannot both have phase s. Their two omission sets remove at most \(2M\) potential common black rows a. Any remaining a gives the vertical-rival support from Section 1. At the midpoint column at most one of the two displayed rows belongs to the prescribed class, so another available row keeps both displayed cells white.

Consequently exactly the following dichotomy is available:

- If both colors have a step with \(n_s(k)>2M\), then the phase has a period at most \(2h-2\) and a complementary translate at distance at most \(h-1\), by the same binary implication argument as before.
- Otherwise, for some color s, the total number of its reflection-closure violations is at most \(Mh\):
  \[
   \#\{(a,b)\in B_s^2:2a-b\in[1,h]\setminus B_s\}
    =\sum_{k\ge1}n_s(k)
    \le 2M\lfloor(h-1)/2\rfloor\le Mh.
  \]

The equality counts each center a and its one same-color endpoint b once; the other endpoint has the opposite color. This gives an exact phase alternative or a quantitative approximate-closure statement. It does not yet turn approximate reflection closure into proximity to an ordinary or quadratic row partition, and a complementary translate of the phase does not make the incomplete alphabets full.

