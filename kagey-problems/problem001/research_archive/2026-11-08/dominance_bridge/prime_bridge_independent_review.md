# Independent review of the prime-alphabet bridge

8 November 2026. I independently checked the argument in `entropy_audit.md`, including its external inputs. No substantive mathematical error was found. The proof establishes the lower bound inside the boundary component, not merely somewhere in the sea graph:

\[
 \lambda_*(h)\ge c h^{1/3}
\]

for all sufficiently large heights and an absolute positive constant `c`.

## Checks completed

**Prime-anchor geometry.** The shared-side rows are `1+t-s` and `1+t+s`. Containment and nondegeneracy force `t>s`. The two integer equations

\[
 x\mid2s(t-s),\qquad r^2=x^2-4(t^2-s^2)
\]

imply `|x|>2(t-s)`. Since `s` is prime and does not divide `t-s`, this forces `s|x`. The resulting congruence `r^2=-4t^2 mod s` is impossible for a prime `s=3 mod 4` distinct from `t`. This excludes every two-pinned mixed four-cell pattern, including all sign choices after reflection. Equal free rows give a degenerate connector instead.

**Two-pinned six-cell patterns.** When the core is longer than the interaction span, both pins lie in the same constant tail. A pinned row-1 point cannot be a right-angle vertex: its two free endpoints are above it and on the same horizontal side, making their dot product positive. Both pins must therefore be endpoints. The completion equation gives `c-b=f-e!=0`; Sidon uniqueness then forces `(c,b)=(f,e)`. The claimed `O(k^2 h^epsilon)` count follows from the fixed-row divisor bound. Repeated points or conflicting rows in one free column are correctly discarded.

**Other pattern counts.** Prescribing a black row-1 cell removes the vertical-translation parameter even when the prescribed cell belongs to the alternative black diagonal. Thus the rooted mixed count is `O(h^(2+epsilon))`. The one-pinned six-cell relation has one genuinely nonzero linear constraint when its five free rows are distinct. The stated repeated-row bounds are valid overestimates. No missing horizontal-window factor occurs: a fixed free column belongs to at most as many translates of one pattern as that pattern has free cells.

**Arithmetic input and alteration.** Theorem 1.1 of [Ramana and Ramaré](https://ramare-olivier.github.io/Maths/dense_primes_israel.pdf), with `K=1`, bounds the energy of all primes in the interval by a constant times their cardinality cubed divided by `log X`. The prime number theorem gives `O(X^3/log^4 X)`, and taking the progression subset cannot increase energy. The deletion estimates, size concentration, and simultaneous Markov bounds leave the claimed Sidon subset of size proportional to `h^(1/3)`. Adding the anchor row 1 preserves Sidon because two primes from the upper half interval cannot sum to another prime in that interval.

**Local lemma and accessibility.** The free arities are correctly `4,3,6,5,4`. Shared pinned cells are constants and do not create dependence. The incident-weight sum is `O(h^epsilon/k)`. [Moser and Tardos, Theorem 1.1](https://arxiv.org/html/0903.0544v3), states the product lower bound used for the number of avoiding words. Each avoiding core, followed by `1^L`, gives a closed path based at `1^L`; every state on that path belongs to the same strongly connected component. Taking the width to infinity at fixed height removes the fixed suffix cost and gives the stated component entropy bound.

## Scope and one clarification

Fix `epsilon` before selecting the alphabet. The simultaneous pattern-count argument is proved for that fixed exponent; choosing `epsilon=1/6` suffices for the theorem. It does not need one alphabet that works simultaneously for every positive exponent.

The result does not establish uniqueness or dominance of this component, dominance of the parity partition, or a quadratic-width construction containing all doubles. In particular, counting many loops at fixed height does not control the height dependence of the width needed to insert all doubles. The constants and the sufficiently-large-height threshold are not made explicit here.
