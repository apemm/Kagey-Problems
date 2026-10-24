# Referee report on the note "Exact ties in coin-turning walks"

Folder `kagey-problems/problem131/S4_aging_note`, files `s4_note.tex`, `s4_intro.tex`,
`s4_body.tex`, `s4_appendix.tex`, `s4_bib.tex`. Read October 24, 2026. No file in the folder was
changed. The note was rebuilt from a copy in a scratch folder (12 pages, no undefined references,
no overfull boxes).

## Summary

The note studies the walk on Z that switches direction at step k with probability c/k, and its
d-state version that moves to each other state with probability theta/(k+d-2). It proves an
exact joint law of counts and last state for a chain that draws its state afresh or repeats it
(Proposition 2.1), exact uniform laws and exact ties at c = 1 and theta = 1 (Proposition 2.3 and
Theorem 2.4), a unique crossing below 1 with a fair start (Proposition 2.6), and the expansion
c_N = 1 - log 2/(log N + gamma + 2 - 2 log 2) + O((log N)^(-3)) for the crossing of the center
and the end (Proposition 2.7, proved in Appendix A through Lemma A.1, Proposition A.2 and the
local limit theorem Proposition A.3).

Verdict. Every proof I read is correct, and every number I recomputed agrees with the text. The
prior-work paragraph is careful and, with one theorem number to fix, accurate. The new content
is modest. The joint law with the last state for d >= 3 or a non-integer weight is a short
induction. Part (b) of the tie results is a 5-line observation once the path expansion is
written. The substantial part is the crossing expansion with its local limit theorem.

## 1. Correctness

### Proposition 2.1 (fresh or repeat)

Checked line by line. With f_T/d = theta/(d theta + T - 1) and 1 - f_T = (T-1)/(d theta + T - 1)
the induction step gives (theta + m_j - 1)/(d theta + T - 1) Q_{T-1}(m'), and the ratio
Q_T(m)/Q_{T-1}(m') = (T/m_j)(theta + m_j - 1)/(d theta + T - 1) closes it. The ratio (2.2) is
Q_T(T/2,T/2)/Q_T(T,0) = binom(T,T/2) theta^(T/2)/(theta+T/2)^(T/2), strictly increasing in
theta, and equal to binom(T,T/2)(T/2)!^2/T! = 1 at theta = 1. Correct. (The ratio needs T >= 2,
which "even T" leaves implicit.)

### Proposition 2.3 (fixed first step)

(a) At c = 1, X_2 is fair and X_{t+1} switches at step t+1 with probability 1/(t+1), which is
the fresh-or-repeat chain with d = 2, theta = 1 (switch probability theta/(d theta + t - 1)).
With T = N - 1, counts (s-1, N-s) and Q_{N-1} = (N-1)!/2^(N-1) = 1/N the formula follows.
Correct.

(b) The path expansion (2.3) and the identity (2.4) are right. Every path with x_1 = +1 and
1 <= s <= N-1 steps +1 switches at least once, each odds omega_t = c/(t-c) is positive and
strictly increasing on (0,2), so the finite sum of products with at least one factor each is
strictly increasing. Correct. The example N = 3, s = 2 (omega_3 + omega_2 omega_3) is right and
equals 1 at c = 1.

Exact check (script `small.py` in the scratch folder, brute force over all 2^(N-1) switch
patterns, rational arithmetic). With X_1 = +1 and c = 1, for N = 2, ..., 6:

| N | law of A_N on 0, 1, ..., N | joint law (s-1)/(N(N-1)), (N-s)/(N(N-1)) |
|---|---|---|
| 2 | 0, 1/2, 1/2 | holds |
| 3 | 0, 1/3, 1/3, 1/3 | holds |
| 4 | 0, 1/4 (four times) | holds |
| 5 | 0, 1/5 (five times) | holds |
| 6 | 0, 1/6 (six times) | holds |

The ratios P_+(A_N = s)/P_+(A_N = N) are strictly increasing along
c = 1/2, 9/10, 1, 11/10, 3/2, 19/10 for N = 3, ..., 6 and equal 1 at c = 1.

### Theorem 2.4 (d states)

(a) At theta = 1, X_2 is uniform (stay probability 1 - (d-1)/d = 1/d) and X_{t+1} moves to each
other state with probability 1/(t+d-1), the fresh-or-repeat chain with theta = 1. Then
Q_{N-1} = (N-1)!(d-1)!/(N+d-2)! = 1/binom(N+d-2, d-1) and (2.5) follows with m = n - e_1.
Correct. The bin count binom(N+d-2, d-1) is right.

(b) The odds theta/(t+d-2-(d-1)theta) have a positive denominator exactly when
theta < (t+d-2)/(d-1), which for t = 2 is the condition theta < d/(d-1). Correct.

The paragraph before the theorem (the Dietz and Sethuraman chain) is right. Their matrices are
P_n = I + G/n for n >= ceil(max |G(i,i)|) + 1 (arXiv v1, p. 4), here ceil((d-1) theta) + 1 <= d+1,
and our step k uses their index n = k+d-2. So "every time n >= d+1" is correct and safe. The
phrase "after one common fresh draw the two chains agree" is right (both chains redraw uniformly
with probability d theta/n, and fresh draws occur infinitely often) but terse; see correction 10.

Remark 2.5: the path probabilities 1/8 and 1/12 are right (1/2 * 1/3 * 3/4 and 1/2 * 1/3 * 2/4).
The CRP probability (d-1)/(k+d-2) and the sum (d-1) log N + O(1) are right.

Figure 1: I recomputed the caption numbers from (2.1) with d = 3, T = 36. At theta = 1/2 the
corner is 9.630 and the center 0.4303 times the uniform value, at theta = 2 they are 0.0347 and
2.061. The caption (9.6, 0.43, 0.035, 2.1) is right.

### Proposition 2.6 (fair first step)

The symmetry identity (2.6) and P_+(A_N = 0) = 0 give (a) at once. In (b) the ratio is the sum of
the two right sides of (2.4) for s and N-s, both in [1, N-1], so it is a finite sum of products
with at least one omega_t each. Continuity, strict increase, the limit 0 as c tends to 0 and the
value 2 at c = 1 follow. Correct. For N = 2 the crossing is c_2 = 2/3 (c/2 = (1 - c/2)/2), which
matches c^(2) = 2/3 in Proposition A.2.

### Appendix A

The gamma bound (A.1). Both cases checked. For c < 1, Gautschi with s = 1-c and Bernoulli's
inequality give -1/y <= theta <= 0. For c > 1, with s = 2-c, the upper bound
y/(y+1-c) <= 1 + 1/(y-1) <= 1 + 2/y uses y >= 2, and the lower bound uses
(1+1/y)^(1-c) >= (1+1/y)^(-1) and y/(y+1-c) >= 1. Correct.

Lemma A.1. The event {A_N = h, X_N = -1} is exactly {T = r, switch at r+1, no switch in
(r+1, N]} for some h <= r <= N-1, and {T = r} is measurable with respect to X_1, chi_2, ...,
chi_r. Flip symmetry doubles it. P(A_{N-1} >= h) = 1/2 since N-1 is odd. The ratio
lambda_{t+1,N}/lambda_{t,N} = t/(t+1-c) <= 1 for c <= 1 gives the bounds. Correct.

Proposition A.2. The equivalence eta_M(c) = 1 iff (1/2) rho(1,M) = c/M, the monotonicity
eta_{M+1}/eta_M = (M+1-c)/M > 1, both halves of the bracket, and c^(3) = (9 - sqrt 57)/2 =
0.72508 from (2-c)(3-c)/2 = 2c are right. The expansion of 1 - c^(M) with
Theta_0'(1) = 1 - psi(1) = 1 + gamma is right. I recomputed the bracket at N = 200:
[c^(101), c^(200)] = [0.887494, 0.898784], as printed.

Proposition A.3 (local limit theorem with a rate). Read step by step.

* Step 1. q_k = c/(k-1+2c) is the switch probability of the fresh-or-repeat chain with d = 2,
  theta = c. The beta-binomial identity and the Hoeffding sandwich are right (condition on B = x
  and split on rx >= y -+ u).
* Step 2. c/k - q_k = c(2c-1)/(k(k-1+2c)) and |c(2c-1)| < 6 on (0,2). The coupling is valid.
  X'_K is a fair sign, the later switches of both processes are independent of the first K steps,
  and X_1, ..., X_{K-1} are drawn from the conditional law given X_K. The sum of
  6/(k(k-1)) over k > K is 6/K. On agreement the counts differ by at most K-1. The bound
  |F(r) - Phi(r)| <= P(h-w <= rB < h+w) + N^(-2) + 6/K follows in both directions.
* Step 3. Delta(h-1) = 0, the summation by parts, Lambda_{N-1} = c,
  Lambda_{r+1} - Lambda_r = Lambda_r (c-1)/(r+2-c) and |Lambda_{r+1} - Lambda_r| <= 2c/h <= 8/N
  are right. The count of r with rb in [h-w, h+w) is at most 2w/b + 1 with b >= 3/8, so at most
  6w + 1. The extra terms add at most (N/2)(N^(-2) + 6/K) <= 1 + 3 sqrt N, so the printed
  6 sqrt N is a valid (loose) bound. For r = N-1 the interval lies in [3/8, 3/4] once N >= 6.
  The conclusion C(w/N + 1/K) = O(sqrt(log N/N)) is right.
* Step 4. Phi(h) = Phi(h-1) = 0, the events {h/r <= B < h/(r-1)} are disjoint with union
  {h/(N-1) <= B < 1}, and on each ceil(h/B) = r. Correct.
* Step 5. Lambda_r = c((r+1)/N)^(c-1)(1 + O(1/N)) from (A.1) at y = N and y = r+1, uniformly in
  c in (0,2). The Lipschitz constant 4 for x^(c-1) on [1/2, 2] is right
  (|c-1| x^(c-2) <= 2^(2-c) <= 4). The final integral
  2c 2^(1-c) B(c,c)^(-1) int_{1/2}^1 (1-b)^(c-1) db = 4^(1-c)/B(c,c) = d_c is right.

The proposition is correct as stated. One observation. The script output shows
|N C_N - d_c| dropping by a factor of 4 each time N is multiplied by 4 (c = 0.75: 5.2e-4,
1.3e-4, 3.3e-5 at N = 400, 1600, 6400), so the true rate looks like O(1/N). The proved rate
sqrt(log N/N) is enough for the expansion, and a one-line remark that it is not sharp would be
honest.

Proof of Proposition 2.7. Theta'(c) = -psi(2-c) - log 4 - 2 psi(c) + 2 psi(2c) gives
Theta'(1) = gamma + 2 - 2 log 2. With epsilon = O(1/log N) from the bracket,
epsilon L = log 2 + O(epsilon^2) + O(sqrt(log N/N)) gives epsilon = log 2/L + O(L^(-3)). Correct.
The second-order remark: Theta''(1) = zeta(2) - 2 zeta(2) + 4(zeta(2) - 1) = pi^2/2 - 4, and
epsilon = log 2/L + Theta''(1)(log 2)^2/(2 L^3) + O(L^(-4)), so the sign of the added term in
c_N = 1 - epsilon is right.

### Numbers at N = 200

My own exact computation (rational arithmetic, transfer over (A, last step), script `n200.py`):

| c | sign of C_200 - E_200 |
|---|---|
| 0.89252 | negative |
| 0.892528 | positive |
| 0.892529 | positive |
| 0.89254 | positive |

So c_200 lies in (0.89252, 0.892528), and linear interpolation gives 0.8925253. The note's
script `verify_aging.py` (run in full, 41 s, all checks passed) gives c_200 = 0.892525269532 by
three methods and confirms the exact sign change at c_200 -+ 1e-6. The expansion gives
0.8931851 and the value with the L^(-3) term is 0.8923633, as printed (0.89319 and 0.89236).
`verify_aging_urn.py` also passes.

## 2. Introduction, credits and self-containment

What is proved matches what is claimed, with two small exceptions.

* The abstract says "every bin ties with the end exactly at c = 1". With a fixed first step bin 0
  has probability 0, so this should say bins 1 to N-1 (correction 1). The introduction says
  "interior bin" without defining it (correction 3).
* The Verification paragraph says "The propositions, the lemma and the theorem are also proved in
  Lean". The map in `lean/PaperD/MAP.md` confirms that every numbered proposition, Lemma A.1 and
  Theorem 2.4 are proved with no named hypothesis (Proposition A.3 uses a weaker binomial tail
  than Hoeffding, which is fine). But the reader is sent to a folder named `PaperD` and to a table
  titled "Paper F by statement label" that uses the old numbers 3.x and B.x and gives the old
  path `paperF/problem131_heavy_aging.tex`, which has been moved to `archive/`. A reader of the
  arXiv note cannot match these. See correction 7.

Credits. I checked the sources I could reach.

* Engländer, Volkov and Wang, arXiv:1904.10953v2, Section 3.1, footnote 1. It says that for
  p_1 = 1/2, p_2 = 1/3, p_3 = 1/4, ..., S_N/N is exactly discrete uniform, credits M. Balázs for
  the Pólya link, and announces a later paper. The note's description and the "shift of one step"
  are accurate (our walk with X_1 = +1 and c = 1 has X_2 fair and switch probability
  1/((k-1)+1)). The paper also proves the zigzag scaling limit for p_n = c/n (Theorem 4(3)), so
  "found the scaling limit" is fair.
* Engländer and Volkov, arXiv:1606.03281v1. Theorem 1 there is the case p_n = 1/n (uniform
  limit). The Beta(a,a) limit for p_n = a/n is Theorem 2. The body cites
  "\cite[Theorem~1]{ev2018}" for the Beta(c,c) limit. Either the published numbering differs, or
  this should be Theorem 2. The bibliography entry does not say which version it follows, unlike
  the entries for ds2007, bc2018 and dls2023. See correction 9.
* Dietz and Sethuraman, arXiv:math/0701798v1. Example 1.1 is the 2-state chain with switch
  probability c/n and the Beta(c,c) limit, and Theorem 1.4 is the Dirichlet limit for the matrix
  Theta. Both citations are accurate. They credit Gantert (1990) for first introducing Example
  1.1. Citing Gantert is optional.
* Bouguet and Cloez, arXiv:1705.02121v1. Proposition 4.1 gives the joint limit
  sum_i nu_i Dir(a theta + e_i) x delta_i, which with equal weights is the Dirichlet law
  size-biased by the current coordinate, as the note says. Proposition 4.5 is the 2-state
  stationary law. Accurate.
* Pradhan, Roy and Ray, arXiv:2605.20116v1. They treat flip probability c/t^alpha, which at
  alpha = 1 is exactly this walk, and give <x^2> ~ t^2/(2c+1) and the run tail l^(-(1+c)) at
  alpha = 1. "A related walk" undersells this. It contains our walk (correction 12).
* Dietz, Lippitt and Sethuraman (Theorem 2.18), Engländer and Volkov 2022 and the
  Engländer and Volkov draft (Chapter 7, Theorem 7.2, Claim 7.1, Section 7.4, Section 5.7) I could
  not open. I did not check them, and the claims are stated with care. The footnote sentence "We
  have not checked the numbering of the published edition" is honest but reads oddly in a posted
  paper. Either check the edition, or give the draft its own bibliography entry and cite only
  that (correction 13).
* The Godrèche and Luck aside on the word "aging" is harmless. Since Pradhan, Roy and Ray use
  "aging" for this very walk, the aside could also be cut.

Self-containment. The mathematics is self-contained. The only outside pointers are the citations
to the two series papers (both arXiv IDs given), the scripts and the Lean folder. Points to fix
before posting, all outside the PDF text:

* `s4_note.tex` lines 2 to 3 (comment "the aging (coin-turning) half of the former Paper F
  draft") and lines 34 to 35 (the unused `\proofpending` macro and its comment) go into the arXiv
  source. Delete them.
* `verify_aging.py` prints "Paper F, Section 3", "Appendix B", "Theorem 3.4" and "research notes,
  not printed". `verify_aging_urn.py` says "the aging walk of Paper F" in its docstring. The note
  names both scripts, so their labels should use 2.x and A.x and drop "Paper F".
* `s4_bib_all.tex` sits in the folder and is not used. Leave it out of the arXiv upload.

## 3. Post or merge

The note is correct, honest about prior work and short, so it can be posted as it stands as a
math.PR note. Its weight rests on the crossing expansion and Proposition A.3, with the exact ties
an easy consequence of known or near-known laws, so I would reframe the abstract and introduction
to lead with the expansion. I see no better host now that Papers A and B are on arXiv.

## 4. Corrections

Line numbers refer to the files as they are now.

| # | File | Line | Old | New |
|---|---|---|---|---|
| 1 | s4_note.tex | 54 | `Hence every bin ties with the end exactly at $c=1$, for every` | `Hence every bin from 1 to $N-1$ ties with the end exactly at $c=1$, for every` |
| 2 | s4_note.tex | 2--3, 34--35 | the comment on the former Paper F draft, the `\proofpending` macro and its comment | delete |
| 3 | s4_intro.tex | 26 | `the center and $E_N=P_N(N)=P_N(0)$ the end. A crossing is a value of $c$ at` | `the center and $E_N=P_N(N)=P_N(0)$ the end. The bins $1,\dots,N-1$ are interior. A crossing is a value of $c$ at` |
| 4 | s4_intro.tex | 59 | `changes sign between $c_{200}\mp10^{-6}$. The` | `changes sign between $c_{200}-10^{-6}$ and $c_{200}+10^{-6}$. Every` |
| 5 | s4_intro.tex | 60 | `propositions, the lemma and the theorem are also proved in Lean~4.33.1 with` | `proposition, the lemma and the theorem are also proved in Lean~4 (version 4.33.1) with` |
| 6 | s4_intro.tex | 33--34 | `$A_N$ is exactly uniform on $\{1,\dots,N\}$.` | unchanged (already exact). Keep the abstract in step with it via correction 1 |
| 7 | s4_intro.tex | 65 | `\nolinkurl{MAP.md} there lists them by label.` | add to `MAP.md` a short table for this note with the current numbers 2.1 to 2.7 and A.1 to A.3 and the current path, then write `The file \nolinkurl{MAP.md} there lists them by the labels of this note.` |
| 8a | s4_body.tex | 116 | `For two states and an integer weight` | `For 2 states and an integer weight` |
| 8b | s4_body.tex | 148 | `[two states, fixed first step]` | `[2 states, fixed first step]` |
| 8c | s4_body.tex | 196 | `two states is part (b)` | `2 states is part (b)` |
| 8d | s4_body.tex | 278 | `For two states Engl\"ander and Volkov` | `For 2 states Engl\"ander and Volkov` |
| 8e | s4_body.tex | 297 | `We return to two states` | `We return to 2 states` |
| 8f | s4_appendix.tex | 5 | `with two states and a fair first step` | `with 2 states and a fair first step` |
| 8g | s4_body.tex | 76--78 | `use all three states, the bands hold the bins that use two, and the disks are the bins that use one.` | `use all 3 states, the bands hold the bins that use 2, and the disks are the bins that use 1.` |
| 8h | s4_body.tex | 139 | `for four values of $\theta$` | `for 4 values of $\theta$` |
| 8i | s4_body.tex | 280 | `example of three steps` | `example of 3 steps` |
| 8j | s4_body.tex | 289 | `along the five` | `along the 5` |
| 8k | s4_appendix.tex | 131 | `The proof has five steps.` | `The proof has 5 steps.` |
| 8l | s4_appendix.tex | 80 | `with the two bounds for $C_N$` | `with the 2 bounds for $C_N$` |
| 9 | s4_body.tex | 9 | `\cite[Theorem~1]{ev2018}` | `\cite[Theorem~2]{ev2018}`, and add to the ev2018 entry in s4_bib.tex `Theorem numbers refer to arXiv:1606.03281v1` (check the published numbering first) |
| 10 | s4_body.tex | 220--222 | `After a shift of the time index by $d-2$, their chain and ours have the same transition probabilities at every time $n\ge d+1$, and after one common fresh draw the two chains agree, so their fractions of time have the same limit.` | `Our step $k$ uses their transition matrix at time $n=k+d-2$, and the two agree for $n\ge d+1$. Both chains redraw a uniform state with probability $d\theta/n$. After the first common redraw they agree, so their fractions of time have the same limit.` |
| 11 | s4_body.tex | 321--324 | `Related fair-start formulas for switch probabilities $1/(n+a)$ appear in~\draftloc{Section~5.7, p.~76}. Its first displayed family is twice a normalized law. We do not use that formula, and derive (a) from the averaging identity~\eqref{eq:aging-fair}.` | `Engl\"ander and Volkov give related fair-start formulas for switch probabilities $1/(n+a)$~\draftloc{Section~5.7, p.~76}. We derive (a) from the symmetry identity~\eqref{eq:aging-fair} instead.` ("averaging identity" is the name of Lemma A.1, so the same name for (2.6) clashes) |
| 12 | s4_intro.tex | 86--87 | `the second moment and the run tail of a related walk.` | `the second moment and the run tail of the walk with switch probability $c/k^\alpha$, which is ours at $\alpha=1$.` |
| 13 | s4_intro.tex | 83--84 | `We have not checked the numbering of the published edition.` | either check the 2025 edition and cite it, or add a separate bibliography entry for the March 18, 2024 draft and drop this sentence |
| 14 | s4_body.tex | 65--66 | `The whole law is explicit on both sides of the tie (Figure~\ref{fig:aging}).` | `Figure~\ref{fig:aging} shows the law below, at and above the tie.` |
| 15 | s4_body.tex | 56 | `For $d=2$ and even $T$,` | `For $d=2$ and even $T\ge2$,` |
| 16 | s4_appendix.tex | 201 | `\le6w+2+6\sqrt N` | `\le6w+2+3\sqrt N` (optional, the printed bound is true) |
| 17 | s4_appendix.tex | after 273 | (none) | optional sentence: `Numerically $\lvert NC_N-d_c\rvert$ decays like $1/N$, so the rate in Proposition~\ref{prop:D-llt} is not sharp.` |

Voice. I found no semicolons or colons in the prose and no em-dashes. Sentences are short and in
the first person plural. "In words," opens 3 paragraphs (s4_body.tex lines 63, 239, 318), which
is a mild tic. The phrase "the two ends" (s4_body.tex line 319) and "the two chains" (line 222)
read better with the word than with a digit, so I left them out of the table.

## 5. Title

"Exact ties in coin-turning walks" fits the first half. It does not fit the fair-start crossing,
which is not an exact tie and is the main analytic result, and the d-state chain is not a walk.
Suggestions:

* "Uniform laws, exact ties and a crossing expansion for coin-turning walks"
* "When the end ties the center in a coin-turning walk"

The first describes the whole note. The second leads with the crossing and ties the note to
Problem 131.
