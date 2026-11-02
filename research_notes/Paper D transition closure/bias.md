# The centred interval of bimodal biases

## Does the interval conclusion require memory near one?

### Takeaway

The actual finite recurrence yields a stronger property than the global two-mode bound: a row is unimodal on the half favoured by the initial bias. This gives the centred-interval conclusion for every superdiffusive memory parameter. The complete finite, transfer, generic classification, actual-law assembly and endpoint chain has passed Lean. The uniform Landau approximation is not needed for connectedness.

### Cited findings

- Guérin, Laulin, Raschel and Simon, Remark 2.1(b), conjecture a centred interval of bimodal biases for every `a` in `(1/2,1)`. Their Theorem 1.1 supplies conditional unimodality. This investigation reread Section 2 through Remark 2.1(b), including the recurrence proof and limiting-unimodality argument; it does not claim a fresh whole-paper reading. [Full text](https://arxiv.org/html/2409.06836v1#S2).
- The previous actual finite two-mode theorem and the new upper-half proof use the same law, `BiasedModes.mass epsilon q n k`. The new proof does not replace it by a density approximation. [Finite proof](../../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalFinite.lean).

### Inferences

For `q >= 1/2`, write

\[
A_n(k)=P_{n,q}(k)-P_{n,1-q}(k)
      =P_{n,q}(k)-P_{n,q}(n-k).
\]

The forward recurrence is

\[
A_{n+1}(k)=(1-r_n(k))A_n(k)+r_n(k-1)A_n(k-1).
\]

It proves `A_n(k) >= 0` for `2k >= n`. At a newly introduced even centre the value is zero by reflection; elsewhere the parents are in the old upper half, and terms outside the support vanish. This establishes actual pointwise reflection dominance, not merely a positive mean.

Use the previously defined augmented first-difference row, but restrict it to `2k+1 >= n`. At time one it has pattern contained in `(+,-)`: its central value is `2q-1 >= 0`, and its outer segment consists of future right-edge differences. Those have pattern `(+,-)` because they are negatives of the left-edge values for bias `1-q <= 1/2`, to which the existing `left_no_PM` theorem applies. This is different from the more complicated outer-edge history for the non-dominant half in the prior global proof.

The positive two-parent recurrence preserves absence of a negative value followed by a positive one. There is one parity exception: when an odd row acquires its central difference, one parent is outside the previous half. That new central difference is nonnegative by reflection dominance, so it cannot start the forbidden pair. The remaining pairs have both relevant parents in the preceding upper half. Thus the actual row has no strict valley on its right half.

The span-two lattice local limit transfers the half-line no-valley property. It also transfers reflection dominance. The floor convention is handled explicitly: for `x >= 0`, the grid point satisfies `N <= 2k_N(x)+1`; for fixed `x>0`, it eventually satisfies `N <= 2k_N(x)`. At `x=0`, density reflection dominance is equality. [Local-limit transfer](../../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalTransfer.lean).

### Gaps

No closed formula for the interval endpoint is obtained. The successful final build target is `PaperD.Modes.BiasIntervalEndpoint`, which imports the full new chain.

## How do the half-line facts give the complete bias classification?

### Takeaway

The bimodal bias set is an open interval `(b_a,1-b_a)`, with `0 <= b_a <= 1/2`; `b_a=1/2` denotes the empty interval. The endpoints themselves are unimodal. A small initial bias approaching zero is handled by the interval theorem, not by claiming uniform profile control of vanishing peaks.

### Cited findings

- The generic reflected-mixture proof, including literal local maxima rather than derivative counts, is recorded in [BiasMixtureInterval.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasMixtureInterval.lean) and [BiasMixtureIntervalModes.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasMixtureIntervalModes.lean).
- The actual ERW assembly derives reflection dominance, half-line unimodality, analyticity, absence of flat intervals and the global two-mode bound from the finite recurrence, smoothing and local-limit inputs. [Assembly](../../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalAssembly.lean).

### Inferences

Put `f_q(x)=q h(x)+(1-q)h(-x)`. Conditional unimodality and reflection dominance imply that `h` is nondecreasing on the negative half-line: a strict descent at `x<y<=0` would have a third witness at `-x` and would contradict unimodality.

For `q>=1/2`, any strict valley gives a strict descent at `x<y<=0`. If the valley's middle point is positive, the right-half no-valley property forces `f_q(0)` below that middle value, so zero replaces it. Conversely, any negative-half descent gives a valley at `(x,y,-x)` by reflection dominance.

For fixed `x<y<=0`, `f_q(x)-f_q(y)` is affine in `q` and is nonpositive at `q=1`. Once it is positive, it remains positive as `q` decreases towards `1/2`. The valley biases are therefore downward closed on `[1/2,1]`. Strict inequalities persist under changes in `q`, so the set is open. Reflection gives the centred interval. Conditional unimodality excludes `q=0,1`.

A strict valley of a continuous, nonnegative, integrable density yields a local maximum on each side: integrability supplies lower points far enough in either direction, and each intervening compact interval contains an interior maximum. Two distinct local maxima conversely yield a strict valley when flat intervals are excluded. The existing all-bias bound excludes a third maximum. When no strict valley exists, the same argument supplies one maximum, and the no-valley condition forces monotonicity towards it and away from it. Hence the endpoint statement is about actual modes, not an unclassified shoulder case.

The existing fourth-moment result guarantees that the interval is nonempty for every `a>=4/5`. The existing uniform near-one result implies `b_a -> 0` as `a -> 1`: for each fixed `eta>0`, eventual bimodality at `q=eta` forces `b_a<eta`. One should not assert `b_a>0` for fixed `a` without an additional argument.

### Gaps

The theorem does not give monotonicity of `b_a` in memory, an explicit endpoint formula or a rate for `b_a -> 0`. Those are separate questions. The full first-priority comparison with Drezner–Farnum remains pending the requested article.

## What was independently checked?

### Takeaway

An exact rational sweep found no failure in 2,560 finite rows, including both parities, negative memory correlation, endpoint biases and the temporal outer boundary. These checks support the debugging of the proof; the general claim rests on Lean and the written argument.

### Cited findings

- [Exact probe](bias_half_probe.py) and [recorded output](bias_half_probe_output.json): times `1,...,64`, memories `{-9/10,-1/2,0,1/5,1/2,7/10,9/10,99/100}`, biases `{1/2,3/5,4/5,99/100,1}`. All arithmetic uses Python fractions. The script uses explicit `require` checks, so optimization cannot disable them.
- [Proof fragment](bias_interval_proof.tex) records the argument for manuscript integration.
- The focused [axiom check](bias_axioms.lean) and [output](bias_axioms_output.txt) cover eight load-bearing declarations, including actual-law assembly and endpoint convergence. The check exited successfully and found only `propext`, `Classical.choice` and `Quot.sound`.

### Inferences

The half-line proof appears to be the missing structural input, rather than improved tail estimates for the near-one approximation. It rules out the disconnected bias bands that a generic reflected mixture with only an at-most-two bound could otherwise exhibit.

An independent review found no mathematical or interface gap in the finite appendix proof and final assembly. It checked both moving-centre parity cases, the one-sided temporal edge history, the use of the same grid point for complementary biases, and derivation of all new analytic and shape properties. The prior conditional unimodality, Fourier representation and smoothing inequality, and actual lattice local limit remain explicit literature inputs.

### Gaps

The finite sweep is not a numerical enclosure of the limiting interval endpoints. No approximate endpoint table has been promoted to a theorem or certificate.
