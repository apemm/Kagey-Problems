# Peter Kagey's Problem 137 — Complete Solution

**Problem** ([peterkagey.com/problems/137](https://peterkagey.com/problems/137/)). Starting from $0$ and repeatedly applying $f(x)=x+1$ and $g(x)=-1/x$ produces every rational number; organizing the values by the least number of steps needed to produce them gives the tree of OEIS [A226247](https://oeis.org/A226247)/[A226248](https://oeis.org/A226248). Let $a(n)$ be the number of elements of rank $n$ (rank $0$ being the root $0$).

> **Question.** Does $a(n) = a(n-1) + a(n-3)$ for all $n \ge 4$?
>
> **Related question 1.** Color a vertex blue when the last map applied is $g$ (and red when it is $f$). Is a vertex blue if and only if its value is negative?
>
> **Related question 2.** Is there a way to characterize all rank-$n$ rational numbers?

## Answers

**Yes**, $a(n)=a(n-1)+a(n-3)$ for all $n\ge 4$ (Theorem 3; the recurrence fails at $n=3$, where $a(3)-a(2)-a(0) = -1$, so $n\ge4$ is sharp). **Yes**, blue $\iff$ negative (Corollary 2). And the rank of every rational is given by a closed formula in terms of its continued fraction expansion — three equivalent forms are given in Theorems 2 and 4 — which yields an explicit enumeration of each rank (Related question 2).

Everything below is self-contained: we prove an exact formula for the rank of every rational, deduce the tree's local structure, and count. The generating function of $a$ is
$$\sum_{n\ge0} a(n)\,t^n \;=\; \frac{1+t^2-t^3}{1-t-t^3},$$
so $a(n) \sim C\,\psi^{\,n}$ with $\psi = 1.465571\ldots$ the *supergolden ratio* (real root of $\psi^3=\psi^2+1$) and $C = 0.7019\ldots$; moreover $a(n) = $ A097333$(n-1)$ and the count of *positive* rationals of rank $n$ is Narayana's cows sequence A000930$(n-1)$.

---

## 1. Setup

Work with the directed graph $G$ on vertex set $\mathbb{Q}$ having an $f$-edge $x \to x+1$ for every $x\in\mathbb{Q}$ and a $g$-edge $x \to -1/x$ for every $x \ne 0$. For $x \in \mathbb{Q}$ let
$$d(x) = \text{length of the shortest directed path from } 0 \text{ to } x \text{ in } G,$$
the least number of applications of $f,g$ producing $x$ from $0$. (Reachability — hence finiteness of $d$ — is part of Theorem 1.)

**Lemma 0 (generations are metric spheres).** In Kimberling's construction (A226247) — row $1 = (0)$, and row $n+1$ lists $c+1$ and $-1/c$ for each $c$ in row $n$, deleting previously generated values — row $n+1$ equals $\{x : d(x)=n\}$. The same set is Kagey's rank $n$ and the set $X_n$ of the Math.SE question.

*Proof.* Induction on $n$ (breadth-first search). Row 1 $=\{x: d(x)=0\}$. If rows $\le n$ are the spheres of radius $<n$, then a value listed in row $n+1$ is an out-neighbour of a vertex at distance $n-1$, so has $d \le n$; deletion of previously generated values forces $d > n-1$, so row $n+1 \subseteq \{d = n\}$. Conversely if $d(x)=n$, the predecessor of $x$ on a shortest path has distance $n-1$, so lies in row $n$, and $x$ appears in row $n+1$. $\blacksquare$

(A value could a priori be produced *twice within the same row*, once as $c+1$ and once as $-1/c'$; Corollary 2(a) shows this never happens, so the construction is unambiguous and the result is a tree.)

## 2. The parent map and the distance function

Define the **parent map** $P:\mathbb{Q}\setminus\{0\} \to \mathbb{Q}$:
$$P(x) = \begin{cases} x-1, & x > 0,\\[2pt] -1/x, & x < 0.\end{cases}$$

Note that $P$ *undoes* an edge of $G$: $P(x) \to x$ is an $f$-edge when $x>0$ and a $g$-edge when $x<0$.

**Lemma 1 (termination).** For every $x \in \mathbb{Q}$, iterating $P$ reaches $0$ after finitely many steps.

*Proof.* If $x>0$, then after $\lceil x\rceil$ subtraction steps the orbit reaches $x - \lceil x \rceil$, which is $0$ (when $x\in\mathbb{Z}$) or lies in $(-1,0)$. For $z\in(-1,0)$ write $z = -r/q$ in lowest terms, $0<r<q$; then $P(z) = q/r > 1$ is positive with lowest-terms denominator $r < q$. Now induct on the denominator $q$ of $x$ for $x \in \mathbb{Q}_{>0}\cup(-1,0)$: if $q=1$ then $x$ is a positive integer and terminates directly; for $q\ge2$, a positive $x$ reaches a point of $(-1,0)$ with the same denominator, whose next iterate is positive with strictly smaller denominator, and terminates by the induction hypothesis. Finally an arbitrary negative $x$ has $P(x)=-1/x>0$. $\blacksquare$

**Definition.** $D(x) =$ number of steps in which the $P$-orbit of $x$ reaches $0$ (so $D(0)=0$, and $D(x) = D(P(x))+1$ for $x\ne0$; $D$ is the unique function satisfying these two properties).

Unwinding the definition gives two identities for free, and two more with a short computation:

**Lemma 2 (increment identities).** For all rational $x$:

- **(D1)** if $x>0$: $\;D(x) = D(x-1)+1$;
- **(D2)** if $x<0$: $\;D(x) = D(-1/x)+1$;
- **(D3)** if $x>0$: $\;D(-1/x) = D(x)+1$;
- **(D4)** if $x<0$: $\;D(x-1) = D(x)+3$.

*Proof.* (D1), (D2) are the definition. (D3): $-1/x<0$, so by (D2), $D(-1/x) = D\!\left(-\tfrac{1}{-1/x}\right)+1 = D(x)+1$. (D4): put $z = x-1 < -1$ and follow four steps of the orbit of $z$, using $x<0$ throughout to fix signs:
$$z \;\xmapsto{P}\; \frac{1}{1-x}\in(0,1) \;\xmapsto{P}\; \frac{x}{1-x}\in(-1,0) \;\xmapsto{P}\; 1-\frac{1}{x} > 1 \;\xmapsto{P}\; -\frac1x = P(x).$$
(For the second membership: $x/(1-x) = -u/(1+u) \in (-1,0)$ where $u=-x>0$.) Hence $D(z) = 4 + D(P(x)) = 4 + (D(x)-1) = D(x)+3$. $\blacksquare$

*Remark.* The computation in (D4), read backwards, says $x-1 = (g\circ f\circ g\circ f\circ g)(x)$: it is exactly the relation $f^{-1} = g f g f g$ from the problem statement (equivalently $(gf)^3=\mathrm{id}$ in $\mathrm{PSL}_2(\mathbb{Z})\cong C_2 * C_3$). The "$3$" in (D4) — cost $5$ of the relator word minus the cancellation $g\cdot g=\mathrm{id}$ — is precisely where the $t^3$ of the recurrence will come from.

**Theorem 1 (distance formula, dynamic form).** Every rational is reachable from $0$, and $d(x)=D(x)$ for all $x\in\mathbb{Q}$.

*Proof.* ($d \le D$.) The reversed $P$-orbit $0 = P^{D(x)}(x),\, \ldots,\, P(x),\, x$ is a directed path in $G$: for each $y$ on the orbit, $P(y)\to y$ is an $f$-edge if $y>0$, and a $g$-edge if $y<0$ (legal since then $-1/y\neq0$). Its length is $D(x)$.

($d \ge D$.) First, every edge $y \to x$ of $G$ satisfies $D(x) \le D(y)+1$:

- $f$-edge, $x>0$: $D(x)=D(y)+1$ by (D1), since $y = x-1$.
- $f$-edge, $x=0$: $D(0)=0 \le D(-1)+1$.
- $f$-edge, $x<0$: $D(x) = D(y) - 3$ by (D4).
- $g$-edge, $x<0$: $D(x)=D(y)+1$ by (D2), since $y=-1/x$.
- $g$-edge, $x>0$: $D(x)=D(y)-1$ by (D3) applied to $x$ (as $y=-1/x$).

Now induct on $n=d(x)$: for $n=0$, $x=0$. For $n\ge1$, let $y\to x$ be the last edge of a shortest path, so $d(y)=n-1$ and, inductively, $D(y)\le d(y)$. Then $D(x)\le D(y)+1 \le d(y)+1 = d(x)$. $\blacksquare$

**Corollary 1 (exact in-neighbour distances).** Let $x\ne0$. The in-neighbours of $x$ in $G$ are $x-1$ (always) and $-1/x$; their distances are:

| | in-neighbour $x-1$ | in-neighbour $-1/x$ |
|---|---|---|
| $x>0$ | $d(x)-1$ | $d(x)+1$ |
| $x<0$ | $d(x)+3$ | $d(x)-1$ |

In particular **exactly one** in-neighbour of $x$ is closer to $0$ than $x$, namely $P(x)$.

**Corollary 2 (tree structure).** (a) Each $x\ne0$ first appears as the image of its unique parent $P(x)$, and never appears twice in one generation (that would require both in-neighbours at distance $d(x)-1$). The construction is therefore a well-defined tree with rank function $d$, independent of any tie-breaking.

(b) The last map applied to reach $x$ (the colour of the edge from its parent) is $f$ exactly when $x>0$ and $g$ exactly when $x<0$. **A vertex is blue if and only if its value is negative** — answering Related question 1 affirmatively.

(c) Children: a vertex $x>0$ has exactly two children, $x+1$ and $-1/x$ (both at rank $d(x)+1$); a vertex $x\in(-1,0)$ has exactly one child, $x+1\in(0,1)$; a vertex $x\le-1$ is a leaf. For a leaf $x<-1$ the blocked $f$-image is not new but **three ranks old**: $d(x+1)=d(x)-3$; for $x=-1$, $x+1=0$ is the root.

*Proof.* All entries read off Corollary 1. For (c), if $x\in(-1,0)$ then $x+1\in(0,1)$ is positive, and Corollary 1 applied to $x+1$ gives $d(x+1) = d(x)+1$; its $g$-image $-1/x$ is its parent. If $x<-1$ then $x+1<0$ and (D4) gives $d(x+1)=d(x)-3$. $\blacksquare$

## 3. Continued-fraction formulas for the rank (Related question 2)

**Negative (Hirzebruch–Jung) continued fractions.** For integers $c_1,\dots,c_k$ define
$$[c_1]^- = c_1, \qquad [c_1;c_2,\dots,c_k]^- = c_1 - \cfrac{1}{[c_2;\dots,c_k]^-}.$$

**Lemma 3.** Every rational $x>0$ has exactly one expansion $x=[c_1;c_2,\dots,c_k]^-$ with $c_1\ge1$ and $c_i\ge2$ for $2\le i\le k$; moreover $c_1=\lceil x\rceil$.

*Proof.* *Existence:* iterate $x \mapsto 1/(\lceil x\rceil - x)$ (stop when $x$ is an integer), recording $c=\lceil x\rceil$. If $x=p/q$ (lowest terms, $q\ge1$) is not an integer, then $\lceil x\rceil q - p \in \{1,\dots,q-1\}$, so $1/(\lceil x\rceil -x) = q/(\lceil x\rceil q-p)$ is $>1$ with strictly smaller lowest-terms denominator; hence the algorithm stops, all digits after the first are $\ge \lceil (\text{something}>1)\rceil \ge 2$, and $c_1 = \lceil x\rceil\ge1$ as $x>0$. *Uniqueness:* if $c_2,\dots,c_k\ge2$ then $[c_2;\dots,c_k]^- > 1$, by induction ($c - 1/y > c-1 \ge 1$ for $y>1$). So $x = c_1 - 1/y$ with $y>1$ lies in $(c_1-1,\,c_1)$, forcing $c_1=\lceil x\rceil$ and $y = 1/(c_1-x)$ when $x\notin\mathbb{Z}$; and an integer admits only the length-$1$ expansion. Induct. $\blacksquare$

**Theorem 2 (rank formula, digit form).** $d(0)=0$; for $x<0$, $d(x) = d(-1/x)+1$; and for $x>0$ with negative continued fraction $x=[c_1;\dots,c_k]^-$ as in Lemma 3,
$$d(x) \;=\; c_1+c_2+\cdots+c_k \;+\; k-1 .$$

*Proof.* By Theorem 1 it suffices to evaluate $D$. The $P$-orbit of $x=[c_1;\dots,c_k]^-$ makes $c_1$ subtractions; if $k=1$ it has reached $0$ in $c_1$ steps. Otherwise it reaches $x - c_1 = -1/[c_2;\dots,c_k]^- \in(-1,0)$, and one flip lands on $[c_2;\dots,c_k]^-$; by induction the total is $c_1 + 1 + \big(\textstyle\sum_{i\ge2}c_i + (k-1)-1\big) = \sum_i c_i + k - 1$. $\blacksquare$

**Explicit enumeration of the ranks.** Combining Lemma 3 and Theorem 2, for $n\ge1$:
$$\{x>0 : d(x)=n\} \;=\; \Big\{[c_1;\dots,c_k]^- \;:\; k\ge1,\; c_1\ge1,\; c_2,\dots,c_k\ge2,\; \sum c_i = n+1-k \Big\},$$
$$\{x<0 : d(x)=n\} \;=\; \Big\{ -1/y \;:\; y>0,\; d(y)=n-1 \Big\},$$
a bijective, collision-free parametrization of rank $n$ by compositions. *Example* ($n=5$): the weight-$5$ digit strings are $(5)$, $(1,3)$, $(2,2)$, giving positives $5,\;[1;3]^-=\tfrac23,\;[2;2]^-=\tfrac32$; the negatives are $-1/y$ over the rank-$4$ positives $y\in\{4,\,\tfrac12\}$, giving $-\tfrac14, -2$. So rank $5 = \{5,\tfrac23,\tfrac32,-\tfrac14,-2\}$, matching the tree.

**Theorem 4 (rank formula, regular-continued-fraction form).** Every rational $x>0$ has a unique regular continued fraction expansion $x=[a_0;a_1,\dots,a_r]$ ($a_0\ge0$, $a_i\ge1$) of **odd length** $r$; with that normalization,
$$d(x) \;=\; \sum_{i \text{ even}} a_i \;+\; 3\!\!\sum_{i \text{ odd}} a_i \;-\;2 .$$
(E.g. $x=\tfrac35=[0;1,1,2]$: $d = (0+1) + 3(1+2) - 2 = 8$.)

*Proof.* Uniqueness of the odd-length form: the two regular expansions of a rational, $[\,\dots,a_m]$ with $a_m\ge2$ (or $m=0$) and $[\,\dots,a_m-1,1]$, have lengths differing by one, so exactly one is odd. Let $E(x)$ denote the displayed formula, extended by $E(0)=0$ and $E(x)=E(-1/x)+1$ for $x<0$. Since $D$ is the unique function with $F(0)=0$ and $F(x)=F(P(x))+1$, it suffices to show $E(x)=E(P(x))+1$ for $x\neq 0$. For $x<0$ this is definitional. For $x>1$: $x-1 = [a_0-1; a_1,\dots,a_r]$ is again a valid odd-length expansion, and $E$ drops by $1$. For $x=1=[0;1]$: $E(1)=3-2=1=E(0)+1$. For $x\in(0,1)$, so $a_0=0$ and $r\ge3$ odd or $(r=1, a_1\ge2)$: we must show $E(x) = E(x-1)+1 = 2 + E\big(\tfrac{1}{1-x}\big)$. Use the classical complement identity (with $u=[b;\text{tail}]\ge1$: $[0;1,b,\text{tail}]=\tfrac{u}{1+u}$ and $[0;b+1,\text{tail}]=\tfrac1{1+u}$, which sum to $1$):

- if $a_1=1$: $\;1-x = [0;a_2+1,a_3,\dots,a_r]$, so $\tfrac1{1-x} = [a_2+1;a_3,\dots,a_r]$, an odd-length form; digitwise, $E$ changes by $+1$ (position $0$) and $-3$ (deleting $a_1=1$), i.e. $E(\tfrac1{1-x}) = E(x)-2$.
- if $a_1\ge2$: $\;1-x = [0;1,a_1-1,a_2,\dots,a_r]$, so $\tfrac1{1-x} = [1;a_1-1,a_2,\dots,a_r]$, again odd length; $E$ changes by $+1$ (position $0$) and $-3$ (position $1$), i.e. $E(\tfrac1{1-x}) = E(x)-2$. $\blacksquare$

## 4. Counting: the main recurrence

Let $r(n) = \#\{x>0: d(x)=n\}$ and $a(n) = \#\{x : d(x)=n\}$.

**Theorem 3.** $a(0)=1$ and $a(n) = r(n)+r(n-1)$ for $n\ge1$, where
$$R(t) := \sum_{n\ge1} r(n)t^n = \frac{t}{1-t-t^3}, \qquad A(t) := \sum_{n\ge0} a(n)t^n = \frac{1+t^2-t^3}{1-t-t^3}.$$
Consequently $\;a(n)=a(n-1)+a(n-3)$ for **all** $n\ge4$, and this fails at $n=3$. Moreover $r(n) = $ A000930$(n-1)$ (Narayana's cows) and $a(n) = $ A097333$(n-1)$.

*Proof.* The map $x\mapsto -1/x$ is a bijection from the negatives of rank $n$ to the positives of rank $n-1$ (by (D2)/(D3)), so $a(n)=r(n)+r(n-1)$ for $n\ge1$. By the enumeration above, $r(n)$ counts tuples $(c_1,\dots,c_k)$, $c_1\ge1$, $c_i\ge2$ ($i\ge2$), with $\sum_i c_i + (k-1) = n$; each tuple contributes $t^{\,c_1} \cdot (t\cdot t^{c_2})\cdots(t\cdot t^{c_k})$, whence
$$R(t) = \sum_{k\ge1} \Big(\sum_{c\ge1}t^{c}\Big) \Big(t\sum_{c\ge2}t^{c}\Big)^{k-1} = \frac{t}{1-t}\sum_{k\ge1}\Big(\frac{t^{3}}{1-t}\Big)^{k-1} = \frac{t}{1-t-t^{3}}.$$
Then $A(t) = 1 + (1+t)R(t) = \dfrac{(1-t-t^3) + t + t^2}{1-t-t^3} = \dfrac{1+t^2-t^3}{1-t-t^3}$. Multiplying out, $(1-t-t^3)A(t) = 1+t^2-t^3$: comparing coefficients of $t^n$ gives $a(n)-a(n-1)-a(n-3) = 0$ for every $n\ge4$ (the numerator has degree $3$), while at $n=3$ it equals $-1$ — matching $a(3)=2$, $a(2)+a(0)=3$. The identification with A000930/A097333 is by their generating functions $\frac{t}{1-t-t^3}$ (shifted) and $\frac{1+t}{1-t-t^3}$. $\blacksquare$

**Growth.** From $A(t)$: $a(n) = C\psi^n + O(|\mu|^n)$ where $\psi=1.4655712319\ldots$ is the supergolden ratio (real root of $t^3=t^2+1$), $\mu$ the complex roots ($|\mu| = \psi^{-1/2}\approx0.826$), and $C = \frac{\psi^2+\psi}{\psi^2+3} = 0.7019310679\ldots$.

**Where the "$-3$" lives (structural view).** Corollary 2(c) sorts each rank into four classes — $r^{+}$: $x>1$; $r^{-}$: $0<x\le1$; $b^{0}$: $-1<x<0$; $b^{1}$: $x\le-1$ — with exact transition rules
$$r^{+\prime} = r^{+}+r^{-},\qquad r^{-\prime} = b^{0},\qquad b^{0\prime} = r^{+},\qquad b^{1\prime} = r^{-},$$
(the $f$-child of any positive is $>1$; the $f$-child of a $b^0$-vertex is in $(0,1]$; $g$ sends $(1,\infty)\to(-1,0)$ and $(0,1]\to(-\infty,-1]$; $b^1$-vertices are leaves). The transfer matrix has characteristic polynomial $t\,(t^{3}-t^{2}-1)$: a positive takes three steps to produce a new positive through the negatives ($r^{+}\to b^{0}\to r^{-}\to r^{+}$), and that three-step detour is the combinatorial shadow of the relation $(gf)^3=\mathrm{id}$, i.e. of identity (D4).

## 5. Geodesic words, and the relation to the earlier Math.SE argument

Reversing $P$-orbits also solves the word problem for this generating process. Reading a path from $0$ as a word in $\{f,g\}$ (leftmost letter applied first), the tree path to any rational is the reversal of its $P$-orbit, and Theorem 1 says these are geodesics. They form the regular language ($m$'s are the $f$-run lengths, and runs are separated by single $g$'s)
$$L \;=\; \Big\{\, f^{m_1} g\, f^{m_2} g \cdots f^{m_j} g^{\,\varepsilon} \;:\; j\ge1,\ \varepsilon\in\{0,1\},\ m_1,\dots,m_{j-1}\ge2,\ m_j\ge1 \,\Big\} \cup \{\text{empty}\},$$
and evaluation at $0$ is a **bijection** from $L$ onto $\mathbb{Q}$ sending word length to rank: the $f$-runs are precisely the negative-continued-fraction digits of Theorem 2 read bottom-up ($m_j = c_1$, $m_{j-1}=c_2,\dots$), with $\varepsilon=1$ exactly for the negatives.

This closes the gap in the (accepted) answer by *mathmasterzach* to the Math.SE question [#5057812](https://math.stackexchange.com/q/5057812): that answer observed that minimal words must avoid the factors $gg$ and $fgfgf$ (from $g^2=\mathrm{id}$ and $(gf)^3=\mathrm{id}$) and must not begin $g\cdots$ or $fgf\cdots$, built the 14-state suffix automaton for the resulting language — which is exactly $L$ — and computed the generating function $\frac{1+t^2-t^3}{1-t-t^3}$ by transfer matrix. What that argument does not establish is that counting *words* counts *rationals*: that every pattern-avoiding word is in fact minimal for its endpoint, that no two such words evaluate to the same rational, and that every rational is realized. Those are exactly the statements supplied here by Theorem 1 and Corollary 2 (uniqueness of the parent), via the explicit formula $d=D$.

## 6. Computational verification

An independent breadth-first search over reduced fractions (exact integer arithmetic) confirmed, through rank $41$ ($14{,}144{,}885$ vertices):

- the rank sizes $a(0),\dots,a(41)$ equal $1, 1, 2, 2, 3, 5, 7, 10, 15, 22, 32, 47, 69, 101, 148, 217, \ldots, 4{,}493{,}437$, satisfying $a(n)=a(n-1)+a(n-3)$ for every $4\le n\le41$ (and failing at $n=3$), and matching A097333 shifted;
- blue $\iff$ negative at every vertex (the last-applied map is $g$ exactly for negative values);
- the structure theorem at every vertex: each positive $x$ has $x-1$ one rank earlier; each negative $x$ has $-1/x$ one rank earlier; each $x<-1$ has $x+1$ exactly **three** ranks earlier; children counts $(2,1,0)$ for positive/$(-1,0)$/$\le-1$ vertices respectively; no value is ever produced twice in a generation;
- both closed-form rank formulas (Theorems 2 and 4) at every vertex of rank $\le 32$;
- the four-class transition rules at every rank;
- term-by-term agreement (values *and* order) with the OEIS data of A226247 and A226248, and rank sizes with A097333.

(Script: `verify.py` alongside this file.)

## 7. Remarks

1. **Positions of the negatives.** Within Kimberling's ordering, the positions of the nonpositive entries are $n + $ A005374$(n)$ (Hofstadter's H-sequence), an observation recorded in A226249 (A. M. Gómez Calderón, 2025). This is consistent with the class dynamics above: the negatives of rank $n$ biject with the positives of rank $n-1$, so their counting function is governed by the same $t^3=t^2+1$ substitution structure that produces A005374.
2. **Sharpness.** The unique failure of the recurrence, $a(3) = a(2)+a(0)-1$, is the boundary effect of the root: $0$'s $g$-image is undefined (it "would be" $\infty$), which removes one length-$3$ word ($fgf$, which returns to $0$) compared to the steady-state automaton.
3. **A226130/A226136.** The OEIS cross-references a variant tree $S'$ (A226130) built from the same maps with different conventions; the same method (parent map + continued-fraction distance) applies there, and the Math.SE question notes a similar conjecture at A226136.

## References

- P. Kagey, [Problem 137](https://peterkagey.com/problems/137/), Open Problem Collection.
- P. Kagey, [Enumerating all fractions by $x\mapsto x+1$ and $x\mapsto-1/x$](https://math.stackexchange.com/q/5057812), Math.SE (2025); accepted answer by mathmasterzach ([#5058406](https://math.stackexchange.com/a/5058406)).
- C. Kimberling, OEIS [A226247](https://oeis.org/A226247), [A226248](https://oeis.org/A226248), [A226249](https://oeis.org/A226249) (2013).
- OEIS [A097333](https://oeis.org/A097333) ($\frac{1+x}{1-x-x^3}$), [A000930](https://oeis.org/A000930) (Narayana's cows), [A005374](https://oeis.org/A005374) (Hofstadter H).
- Negative ("Hirzebruch–Jung") continued fractions: standard; all facts used are proved above (Lemma 3).

---
*Solution prepared 2026-08-23. All results verified computationally through rank 41; all proofs self-contained.*
