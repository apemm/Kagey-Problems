# Reflected mixtures and the bias interval

## Which model-specific facts suffice?

### Takeaway

The centred-interval conclusion follows from two stronger finite-chain facts:
reflection dominance and absence of a valley on the dominant half-line. Uniform
Landau approximation alone does not give this classification.

### Cited Findings

- The existing finite first-difference theorem excludes three local maxima after
  lattice local-limit transfer. Its analytic no-flatness input is proved from
  the conditional Fourier smoothing identity. These are already in
  [BiasLimitCore.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasLimitCore.lean)
  and [BiasLimitTransfer.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasLimitTransfer.lean).
- The separate finite-chain investigation supplies dominant-half no-valley and
  reflection dominance through the actual lattice local limits. Its source is
  [BiasIntervalTransfer.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalTransfer.lean).

### Inferences

Write \(f_q(x)=q h(x)+(1-q)h(-x)\). Assume that \(h\) is unimodal,
\(h(-x)\le h(x)\) for \(x\ge0\), and every \(f_q\), \(q\ge1/2\), has
no strict valley entirely inside \([0,\infty)\).

A strict valley is a triple \(x<y<z\) satisfying
\(f_q(y)<\min\{f_q(x),f_q(z)\}\). For \(q\ge1/2\), a valley exists if
and only if some \(x<y\le0\) satisfy \(f_q(x)>f_q(y)\). To prove the
forward direction, the left point must be negative. If the middle point is
positive, the no-right-valley property forces
\(f_q(0)\le f_q(y)<f_q(x)\), giving a descent to zero. Conversely, a
negative-half descent gives the valley \((x,y,-x)\), because reflection
dominance gives \(f_q(-x)\ge f_q(x)>f_q(y)\).

The same argument at \(q=1\) shows that \(h\) is nondecreasing on the
negative half-line: a decrease there would create a valley of the unimodal
conditional density.

Fix a strict descent at \(x<y\le0\). Its height difference is
\[
 D(q)=q\{h(x)-h(y)\}+(1-q)\{h(-x)-h(-y)\}.
\]
Here \(D(1)\le0\). If \(D(q)>0\), affinity implies \(D(r)>0\) for all
\(1/2\le r\le q\). Thus the valley set is downward closed on
\([1/2,1]\). Strict inequalities make it open in \(q\), and
\(f_{1-q}(x)=f_q(-x)\) makes it symmetric. It is consequently exactly
\((b,1-b)\) for some \(b\in[0,1/2]\), with the empty case represented by
\(b=1/2\).

### Gaps

The generic argument does not prove \(b>0\) at every fixed memory below one.
It allows the full interior interval \((0,1)\). A strict positivity result
would need stability of the conditional mode and its tails under a small
reflected admixture.

## Does the interval describe literal modes?

### Takeaway

Yes. The valley criterion is equivalent to two distinct local maxima for a
continuous nonnegative integrable function without flat intervals. Together
with the established at-most-two bound it describes the entire mode set.

### Cited Findings

- The local-maxima separation lemma is already proved in
  [BiasLimitCore.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasLimitCore.lean).
- The new converse and complete classification are implemented in
  [BiasMixtureIntervalModes.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasMixtureIntervalModes.lean).

### Inferences

A positive value of an integrable nonnegative function has a lower value
somewhere on each side. Otherwise a positive constant would be integrable on
an infinite ray. Apply this to the two upper points of a strict valley and
maximize on the resulting compact intervals. Both maximizers are interior,
and they lie on opposite sides of the valley point. Conversely, two local
maxima have a lower value between them when constant intervals are excluded.

If there is no valley, the same compact-interval argument supplies a local
maximum. It is global: a higher value on either side, together with the strict
decrease next to the local maximum, would create a valley. Absence of a valley
then makes the function nondecreasing before that maximum and nonincreasing
after it. No-flatness makes its local maximum unique. This includes the bias
endpoints and rules out treating stationary shoulders as extra modes.

### Gaps

The generic files require continuity, integrability, nonnegativity and
no-flatness as explicit interfaces. The final elephant-walk assembly must
derive these from the previously proved density/Fourier results and the
published probabilistic inputs. The generic file alone is not that assembly.

## What is formally checked?

### Takeaway

Both generic modules compiled successfully in a focused Lake build, with no
errors. The four warnings were two deprecated `push_neg` uses and two
unnecessary `simpa` uses. The interval conclusion is proved rather than
assumed. The final revision audit records the complete import and axiom check.

### Cited Findings

- [BiasMixtureInterval.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasMixtureInterval.lean)
  proves the affine descent argument, symmetry, openness and interval endpoints.
- [BiasMixtureIntervalModes.lean](../../kagey-problems/problem131/lean/PaperD/Modes/BiasMixtureIntervalModes.lean)
  proves the mode equivalence and complete one-mode/two-mode classification.

### Inferences

The crucial new input is the dominant-half finite-chain theorem. Once it is
established, the mixture argument applies at every superdiffusive memory,
rather than only near one. The previous near-one two-peak theorem then implies
that the lower bias endpoint tends to zero, but it does not give a numerical
rate for that convergence.

### Gaps

The precise source-level and build status must be read from the final audit;
this note does not substitute for its output. No claim is made here about
continuity or monotonicity of the bias endpoint as a function of memory.
