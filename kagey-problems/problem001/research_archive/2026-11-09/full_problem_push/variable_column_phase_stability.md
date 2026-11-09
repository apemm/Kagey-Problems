# Dense alphabets force a protected column law

9 November 2026. If the row partition is already ordinary or quadratic, dense Cartesian alphabets force the corresponding protected column phase without any periodicity assumption. The complete proof, including the strengthened quadratic threshold, passed independent review.

Write \(q(n)=n(n-1)/2\bmod2\). Let the balanced row coloring be
\[
 c(y)=\kappa q(y)+\alpha y+\beta,\qquad 1\le y\le h,
\tag{1}
\]
where either \(\kappa=0,\alpha=1\), or \(\kappa=1\) and the stated coloring is balanced. At each integer column x, choose a phase \(t_x\in\mathbb F_2\) and an alphabet
\[
 A_x\subseteq\{y:c(y)=t_x\},\qquad |A_x|\ge k.
\]
Suppose this Cartesian product has no singleton-axis rival for the complete pair set between the two row blocks.

**Theorem.** The column phase has the form
\[
 t_x=\kappa q(x)+\gamma x+\delta
\tag{2}
\]
provided the corresponding condition holds:
\[
 \begin{cases}
 3k>3\lceil h/2\rceil-\lfloor(h-4)/2\rfloor,&\kappa=0,\\
 4k>4\lceil h/2\rceil-2\lfloor(h-4)/4\rfloor,&\kappa=1.
 \end{cases}
\tag{3}
\]
The same conclusion holds on any finite consecutive interval of at least five columns.

In particular, ordinary row parity needs only \(k>h/3+2\), and a balanced quadratic row partition needs only \(k>3h/8+2\). Thus alphabets of size at least \(0.49h\) satisfy the hypothesis for all sufficiently large h, even when the alphabets vary arbitrarily from column to column.

## 1. Two local rectangle templates

For an integer vertical translation y, use the adjacent vectors
\[
 (1,2),(2,-1),\qquad\text{or}\qquad(1,3),(3,-1).
\]
They give the rectangles
\[
\begin{aligned}
 T_2(x,y)&=\{(x,y),(x+1,y+2),(x+2,y-1),(x+3,y+1)\},\\
 T_3(x,y)&=\{(x,y),(x+1,y+3),(x+3,y-1),(x+4,y+2)\}.
\end{aligned}
\tag{4}
\]
Both have four distinct corner columns. Every \(2\le y\le h-3\) places both templates in the strip.

For any lattice rectangle with corner coordinates \((x_i,y_i)\),
\[
 \bigoplus_i q(x_i)=\bigoplus_i q(y_i).
\tag{5}
\]
Indeed, the mixed finite difference of \(q\) is the product of the two increments modulo two; orthogonality equates the horizontal and vertical products modulo two. The linear term in (1) has zero four-corner sum. Thus
\[
 \bigoplus_i c(y_i)=\kappa\bigoplus_i q(x_i).
\]
Put \(s_x=t_x+\kappa q(x)\). If \(\bigoplus_i s_{x_i}=1\), the actual row-color vector and prescribed column-phase vector differ in an odd number of positions.

## 2. A wrong four-corner sum survives the omitted rows

For ordinary row parity, shifting y by one complements all four row colors. For a quadratic row coloring, shifting y by two does so, since
\[
 q(n+2)+q(n)=1.
\]
For ordinary parity, an odd mismatch count can therefore be made exactly one by choosing an appropriate residue class of y modulo two. The same corner is the unique mismatch throughout this class. There are at least \(\lfloor(h-4)/2\rfloor\) available translates. At each of the three matching corners, at most \(\lceil h/2\rceil-k\) rows of the correct color are missing from its alphabet. Since each corner row is an injective function of y, these three alphabets exclude at most
\[
 3(\lceil h/2\rceil-k)
\]
of the translates.

For a quadratic coloring, both templates' vertical offset parity vectors have exactly two zeros and two ones. Shifting y by one therefore changes exactly two of their four row colors; shifting by two complements all four. The four row-color vectors obtained modulo four are distinct and consist of two complementary pairs. When the mismatch count is odd, exactly one vector from each complementary pair has precisely one mismatch. Thus there are two residue classes, containing at least \(2\lfloor(h-4)/4\rfloor\) translates in total, with exactly three matching corners. Their mismatching corners need not be the same. Counting omissions over all four columns now excludes at most
\[
 4(\lceil h/2\rceil-k)
\]
translates: a specified omitted row at a specified corner determines at most one y, even across the two residue classes.

In either case, condition (3) leaves a translate whose three matching corners belong to their column alphabets.

Choose those three black cells. The fourth corner has row color opposite to the prescribed class at its column, so it is white regardless of the chosen letter there. Its row and the actual black row at that column form a pair from the complete row-block graph. The tilted rectangle therefore has a singleton-axis rival, a contradiction.

Consequently both templates in (4) have zero sum of the s-values:
\[
 \begin{aligned}
 s_x+s_{x+1}+s_{x+2}+s_{x+3}&=0,\\
 s_x+s_{x+1}+s_{x+3}+s_{x+4}&=0.
 \end{aligned}
\tag{6}
\]

## 3. The recurrences determine the phase

Set \(d_x=s_x+s_{x+1}\). Equation (6) says
\[
 d_x=d_{x+2},\qquad d_x=d_{x+3}.
\]
On the full integer line these force d to be constant. On a finite interval of at least five columns, the distance-two relations and the first available distance-three relation already connect all consecutive bonds; the remaining bonds follow by distance two. Hence \(s_x=\gamma x+\delta\), proving (2).

The theorem classifies the phase after the row partition is known. It does not yet show that every dense variable-column box uses an ordinary or quadratic row partition. The period-two and period-four results establish that additional conclusion under their stated period hypotheses.
