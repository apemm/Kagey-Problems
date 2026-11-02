# Transition uniqueness and the separation of modes

Research record, 1 November 2026. This folder contains candidate results and
exploratory interval computations. It is not part of the released certificate.
No claim of a Lean-verified unique elephant transition is made here.

## Can the transition be proved unique?

### Takeaway

A differentiated-smoothing argument gives a complete analytic route to a
positive parameter derivative near the existing transition bracket. The local
Arb prototype returns

\[
 0.6889315 < \partial_a g_a''(0) < 0.6890685,
 \qquad 0.66881285\le a\le0.66881287.
\]

This is a candidate rigorous interval-arithmetic result, pending independent
review of the derivation and a kernel-checkable numerical certificate. It is
not a theorem established by the existing Lean library. The existing threshold
bracket lies strictly inside this interval.

### Cited findings

- The existing certificate proves a sign bracket, continuity, and exclusion of
  zeros outside its tiny unresolved interval. Its proof does not differentiate
  the infinite-frequency tail. The exact unresolved endpoints are
  `1838418790980431/2748779069440000` and
  `45960469774511/68719476736000`. Sources:
  [certificate](../../kagey-problems/problem131/paperD/certify_threshold.py),
  [stored run](../../kagey-problems/problem131/paperD/data/threshold_zero_0.668_0.6712.txt),
  [proof](../../kagey-problems/problem131/paperD/online_resource_body.tex).
- The conditional-first-step law obeys the distributional smoothing equation,
  has a density, and has the moment recursion used by the certificate.
  The Fourier decay proof in Theorem 2.5, Step 4, is a bootstrap from that
  equation. Source: [Guérin, Laulin and Raschel](https://arxiv.org/pdf/2308.14630).
- The successful computations are reproducible with
  [probe_parameter_tail.py](probe_parameter_tail.py) and
  [its output](probe_parameter_tail_output.json). These files do not change
  the released certificate or its stored records.

### Inferences

The following derivation is new work in this research folder. It gives the
mathematical route tested by the prototype. It does not infer a derivative
bound from a uniform approximation error.

Write \(\phi=\phi_a\), \(p=(1+a)/2\), \(x=t v^a\),
\(y=t(1-v)^a\), and

\[
 B_a\phi(y)=p\phi(y)+(1-p)\phi(-y).
\]

The exact equation is

\[
 \phi_a(t)=\int_0^1\phi_a(x)B_a\phi_a(y)\,dv.
\]

Put \(f(t)=|\phi(t)|\), \(u(t)=|\partial_t\phi(t)|\), and
\(w(t)=|\partial_a\phi_a(t)|\). On compact real \((a,t)\) sets, the
complex-parameter moment series and its differentiated series converge
uniformly. Thus the partial derivatives exist there. Differentiation under
the integral over \(v\) is legitimate: the arguments remain in a compact
\(t\) set, and \(v^{a_-}|\log v|\) is bounded when \(a_->0\).

Conjugate symmetry gives even moduli for \(f,u,w\). Differentiating in
frequency therefore gives

\[
 u(t)\le\int_0^1\{v^a u(x)f(y)+(1-v)^a f(x)u(y)\}\,dv. \tag{1}
\]

Differentiating in memory gives

\[
 w(t)\le\int_0^1\{w(x)f(y)+f(x)w(y)\}\,dv+S(t), \tag{2}
\]

where

\[
 S(t)\le\int_0^1\{x|\log v|u(x)f(y)
       +y|\log(1-v)|f(x)u(y)+f(x)f(y)\}\,dv. \tag{3}
\]

The last term in (3) is the derivative of the mixing weight. Its coefficient
is correct: \(p'=1/2\) and
\(|\phi(y)-\phi(-y)|\le2f(y)\).

Assume the existing real Fourier certificate supplies \(\beta>4\),
\(T_3\ge2^aT_2\), \(C>0\), and \(R<1\), uniformly on the parameter
interval, such that

\[
 f(t)\le Ct^{-\beta}\quad(t\ge T_2),\qquad
 H_\beta(t):=2\int_0^{1/2}f(tv^a)(1-v)^{-a\beta}\,dv\le R
 \quad(t\ge T_3). \tag{4}
\]

The cell-and-tail proof already establishes the second bound in (4): its
quantity \(R\) is an upper bound for this half-interval integral. It also
establishes the first bound on \([T_2,T_3]\), not only beyond \(T_3\).

**Frequency derivative.** The moment bound gives \(u\le M\), where
\(M\ge\sqrt{\mathbb E L_a^2}\). Suppose cells establish
\(u(t)\le D_1t^{-\beta}\) on \([T_2,T_3]\). At a possible first
contact beyond \(T_3\), split (1) at \(v=1/2\). On its first half,
use the global bound \(M\) for the derivative at the smaller argument
and the candidate bound at the larger argument. The result is

\[
 u(t)\le t^{-\beta}(A_1+RD_1),\qquad
 A_1=\frac{MC2^{a(\beta-1)}}{a+1}. \tag{5}
\]

Consequently, \(D_1>A_1/(1-R)\), together with the cell bound, proves
\(u(t)\le D_1t^{-\beta}\) for every \(t\ge T_2\). This is an
inhomogeneous first-contact argument. It does not assume derivative decay.

**Parameter derivative.** Set \(\gamma=\beta-1\), assume
\(a\gamma>1\), and let \(M_a\) bound \(w\) on \([0,T_2]\).
Cells give an initial bound \(D_at^{-\gamma}\) on \([T_2,T_3]\).
For \(v_0=(T_2/t)^{1/a}\), the smaller-argument term in (2) is bounded by

\[
 2C2^{a\beta}t^{-\beta-1/a}
 \left(M_aT_2^{1/a}
 +\frac{D_aT_2^{1/a-\gamma}}{a\gamma-1}\right).
\]

Indeed, integrate the constant bound on \([0,v_0]\), and then integrate
\(D_at^{-\gamma}v^{-a\gamma}\) from \(v_0\) to \(1/2\).
The larger-argument term contributes at most \(RD_at^{-\gamma}\),
since \(H_\gamma\le H_\beta\). Define

\[
 J=2C2^{a\beta}T_3^{\gamma-\beta-1/a},\quad
 \kappa=R+\frac{JT_2^{1/a-\gamma}}{a\gamma-1},\quad
 A_0=JM_aT_2^{1/a}.
\]

The forcing terms in (3) satisfy \(S(t)\le A_St^{-\gamma}\), where

\[
 A_S=MC2^{a(\beta-1)}
 \left(\frac{\log2}{a+1}+\frac1{(a+1)^2}\right)
 +D_1(\log2)R+\frac{CR}{T_3}. \tag{6}
\]

The first term uses the exact integral
\(\int_0^{1/2}v^a(-\log v)\,dv
=2^{-a-1}\{\log2/(a+1)+(a+1)^{-2}\}\).
The second uses \(-\log(1-v)\le\log2\) and (4).
The final term bounds the mixing-weight contribution by
\(CRt^{-\beta}\le(CR/T_3)t^{-\gamma}\).

Thus a first contact would imply

\[
 w(t)\le t^{-\gamma}(A_0+A_S+\kappa D_a).
\]

If \(\kappa<1\) and
\(D_a>(A_0+A_S)/(1-\kappa)\), the candidate tail is valid for all
\(t\ge T_2\). The prototype takes twice the maximum of the necessary
initial and forcing constants, providing strict slack.

For \(\gamma>3\), dominated differentiation now proves

\[
 \partial_a g_a''(0)=-\frac1\pi\int_0^\infty
 t^2\operatorname{Re}(\partial_a\phi_a(t))\,dt,
\]

with tail error at most
\(D_aT_3^{3-\gamma}/\{\pi(\gamma-3)\}\).
Continuity of this derivative follows from the same uniform domination.

**Finite cells and parameter remainder.** The prototype differentiates the
finite parameter Taylor polynomial. The remainder is bounded using

\[
 \sum_{i>K}i q^{i-1}
 =\frac{q^K\{(K+1)-Kq\}}{(1-q)^2},
\]

and Cauchy's coefficient estimate with the extra factor \(1/\rho\).
The omitted moment series is differentiated by Cauchy's estimate on a disc
of radius \(\rho-w\) around each real parameter. Its bound is
\(\tau_k(t)/(\rho-w)\). For the frequency-cell remainder, the prototype
uses degree 48 and bounds the actual high derivative by the noncancelling
complex-parameter coefficient majorant, not by a probability-moment bound
that would be invalid at complex parameters.

The tested constants are \(\beta=8\), \(\gamma=7\), \(T_2=6\),
\(T_3<9.538586\), \(C<0.016322\), \(R<0.081029\),
\(D_1<0.995687\), \(M_a<3.538318\), \(D_a<1.946410\), and
\(\kappa<0.081029\). The resulting Fourier-tail error in the
parameter derivative is below \(1.872\cdot10^{-5}\).

### Gaps

1. The derivation above needs an independent mathematical review, particularly
   the differentiated smoothing identity and all half-interval factors.
2. The prototype uses Arb, not a Lean kernel certificate. Its gamma and
   reciprocal-gamma values, power series, complex Cauchy bounds, cell bounds,
   and final interval operations are not covered by the current Lean library.
3. Existing `Modes/GammaMoments.lean` proves qualitative gamma convexity and
   elementary moment bounds. It does not certify these high-precision gamma
   evaluations. Existing threshold records are explicitly outside Lean
   coverage and cannot silently become trusted premises for this new result.
4. To publish uniqueness under the present formal-verification requirement,
   export rational enclosures with checkable proofs for the transcendental
   evaluations, then replay the recurrence, Taylor, and tail arithmetic in
   Lean. The differentiated integral inequalities and the first-contact
   propagation must also be linked to the actual characteristic function.
5. No manuscript, release certificate, or author statement has been changed.

## What does quartic nondegeneracy imply about the modes?

### Takeaway

A second prototype bounds the fourth derivative away from zero throughout
the larger transition interval. Combined with the positive parameter
derivative, this would yield a unique supercritical pitchfork, with square-root
mode separation and quadratic height gain. Those ERW conclusions remain
candidate results until the numerical verification gap above is closed.

### Cited findings

- [probe_transition.py](probe_transition.py), using the reviewed real Fourier
  bootstrap with \(\beta=8\), gives
  \(-0.081<g_a^{(4)}(0)<-0.079\) for
  \(a\in[0.6688,0.6692]\). Its total Fourier/truncation error is below
  \(1.41\cdot10^{-14}\). The same calculation gives
  \(0.17497<g_a^{(6)}(0)<0.18503\). See
  [the saved output](probe_transition_output.json).
- The existing analytic-density proof supplies spatial analyticity and the
  strict one-mode/two-mode classification. Its new numerical extension to
  fourth derivatives is not automatically covered by that formalization.
  Sources: [AnalyticCharacteristic.lean](../../kagey-problems/problem131/lean/PaperD/Modes/AnalyticCharacteristic.lean),
  [RevisionShape.lean](../../kagey-problems/problem131/lean/PaperD/Modes/RevisionShape.lean).

### Inferences

Let \(q(a)=g_a''(0)\), let \(a_*\) be a zero, and write
\(r_*=g_{a_*}^{(4)}(0)<0\). The uniform Fourier bound with exponent greater
than five gives joint continuity of the first four spatial derivatives in
\((a,x)\). Evenness eliminates odd derivatives at zero. At \(a_*\),
Taylor's theorem gives \(g_{a_*}'(x)<0\) for sufficiently small positive
\(x\). The shape dichotomy therefore puts the critical density in the
strictly unimodal branch.

If \(a_n\to a_*\) through bimodal parameters with positive modes \(c_n\),
then \(c_n\to0\). Otherwise select a small positive point where
\(g_{a_*}'<0\). Joint continuity makes the nearby derivatives negative
there, contradicting monotone increase before modes bounded away from zero.

Taylor's theorem applied to the derivative at a positive mode gives, for
some \(\xi_a\in(0,c(a))\),

\[
 0=q(a)c(a)+\frac16g_a^{(4)}(\xi_a)c(a)^3.
\]

Hence, without needing a parameter derivative,

\[
 \frac{c(a)^2}{q(a)}\longrightarrow-\frac6{r_*},\qquad
 \frac{g_a(c(a))-g_a(0)}{q(a)^2}\longrightarrow-\frac3{2r_*}. \tag{7}
\]

The second limit follows from the fourth-order Taylor formula for the height
and the first limit. This is a square-root law in central curvature. Calling
it a square-root law in memory before proving \(q'(a_*)>0\) would be wrong.

If the differentiated-smoothing certificate is fully validated, let
\(A=q'(a_*)>0\). Then the positive derivative on an interval containing
every possible zero proves that \(a_*\) is unique. Since
\(q(a)\sim A(a-a_*)\), (7) becomes

\[
 c(a)\sim\sqrt{-6A/r_*}\sqrt{a-a_*},\qquad
 g_a(c(a))-g_a(0)\sim-\frac{3A^2}{2r_*}(a-a_*)^2.
\]

These are the most substantial prospective additions from this branch.

### Gaps

- The numerical fourth-derivative enclosure requires the same kernel-checkable
  transcendental and interval infrastructure as the parameter certificate.
- The full general pitchfork argument has not been integrated in Lean. A
  standalone Taylor amplitude prototype is preserved in this research folder
  and does not establish an ERW claim.
- No claim is made that the mode is analytic in the original memory parameter.
  The displayed asymptotics need only the regularity and nondegeneracy stated
  above.

## How does this compare with the literature?

### Takeaway

The checked primary sources do not supply uniqueness of the fair-start modal
transition, differentiated-memory Fourier tails, or the above mode-separation
law. The nearest sources supply the smoothing equation, unimodality of the
conditional-first-step law, and a broader conjecture about initial bias.
This is a bounded novelty assessment, not an exhaustive proof of priority.

### Cited findings

- Guérin, Laulin and Raschel, *A fixed-point equation approach for the
  superdiffusive elephant random walk*, gives the underlying distributional
  equation, moments, and Fourier bootstrap. Freshly checked: the opening
  results and the density proof's Step 4. I did not reread all 38 pages in
  this pass. [Full text](https://arxiv.org/pdf/2308.14630).
- Guérin, Laulin, Raschel and Simon, *On the limit law of the superdiffusive
  elephant random walk*, proves unimodality for first-step parameter one.
  Remark 2.1(b) conjectures a threshold in initial bias separating unimodal
  and bimodal mixtures. Freshly checked: the introduction, theorem statements,
  modal discussion, and that remark, including its adjacent log-concavity
  discussion. I did not reread all 25 pages in this pass.
  [Full text](https://arxiv.org/pdf/2409.06836).
- González Rangel, *Asymptotics for the Laplace transform of the Elephant
  Random Walk via Schwarz-Christoffel mappings*, July 2026, studies the
  large-time Laplace transform of the finite walk. The complex continuation
  used there is in the generating-function variable. It does not directly
  provide a complex-memory tail bound for the limit characteristic function.
  Freshly checked: abstract, introduction, principal theorem, and the
  asymptotic extraction in Section 2. No full-paper read is claimed.
  [Full text](https://arxiv.org/html/2607.15125v1).

### Inferences

- A rigorously established unique modal transition and its memory pitchfork
  would answer a different question from the classical diffusive/superdiffusive
  transition at memory \(p=3/4\).
- The useful technical addition is the inhomogeneous differentiated smoothing
  certificate. Its proof derives tail control for parameter sensitivity from
  compact parameter analyticity and a real Fourier bootstrap. The fact that
  a finite Taylor polynomial has a positive derivative is insufficient by
  itself.
- The 2026 Laplace-transform preprint is relevant background but does not close
  this gap. Its fixed-parameter asymptotics must not be interchanged with
  parameter differentiation without a separate uniform estimate.

### Gaps

- Searches for the exact ERW/pitchfork and ERW/unique-bimodality combinations
  found no primary result resolving this problem. Absence in these searches
  is not proof that none exists.
- The general smoothing-transform sensitivity literature has not been read
  exhaustively. Before a priority claim, inspect work on parameter-dependent
  smoothing transforms and urn limits beyond the ERW papers listed here.
- The user requested full formal verification of every new addition. The
  promising numerical theorem is therefore deliberately excluded from the
  manuscript until the explicit proof obligations in the first section close.
