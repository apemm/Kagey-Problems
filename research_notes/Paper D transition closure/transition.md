# Closing the fair transition window

## Does the parameter derivative have a certified positive sign?

### Takeaway

The differentiated smoothing argument survives an independent audit. The new
certificate checks, on the interior of the interval

\[
 I=[0.66881285,0.66881287],
 \qquad 0.68<\partial_a g_a''(0)<0.70,
 \qquad -0.09<g_a^{(4)}(0)<-0.07.
\]

The released zero bracket is strictly inside this interval. These bounds use
Arb with outward enclosures. They do not claim that the numerical gamma and
Cauchy evaluations have been replayed by Lean's kernel. The existing reviewed
certificate has the same numerical boundary.

### Cited findings

- The exact old bracket and its outside-sign proof are in
  [the reviewed certificate](../../kagey-problems/problem131/paperD/certify_threshold.py).
  Its endpoints are
  \(z_-=1838418790980431/2748779069440000\) and
  \(z_+=45960469774511/68719476736000\).
- The complex moment bound, reciprocal-gamma majorant, geometric series tail,
  Cauchy Taylor estimate and real Fourier bootstrap are proved in Section S10
  of [the existing supplement](../../kagey-problems/problem131/paperD/online_resource_body.tex).
- The differentiated smoothing prototype is in the preceding investigation's
  [derivation](../Paper%20D%20transition%20and%20modes/transition.md). The present
  [production certificate](../../kagey-problems/problem131/paperD/certify_transition.py) replaces adaptive numerical
  constants by conservative fixed rational constants and fails closed if any
  check fails. Its final output is
  [the certificate record](../../kagey-problems/problem131/paperD/data/transition_derivative_certificate.json).

### Inferences

Write \(\phi_a\) for the characteristic function conditional on the first step
being positive and \(p=(1+a)/2\). The exact smoothing equation is

\[
 \phi_a(t)=\int_0^1\phi_a(tv^a)
 \{p\phi_a(t(1-v)^a)+(1-p)\phi_a(-t(1-v)^a)\}\,dv.
\]

The complex moment series is locally uniformly convergent in both variables.
Indeed, on the square \(|\Re z-a_0|,|\Im z|\le\rho\), the reviewed moment
lemma gives \(|c_n(z)|\le\widetilde A\widetilde B^n/\Gamma(1+n\alpha)\)
with \(\alpha>1/2\). The ratio majorant tends to zero, including after any
fixed number of frequency derivatives. Cauchy's estimate on a smaller
parameter disc therefore proves local uniform convergence of the parameter
derivative series. This gives the actual derivative \(\partial_a\phi_a\),
not a derivative of a real approximation bound.

Put \(f=|\phi_a|\), \(u=|\partial_t\phi_a|\),
\(w=|\partial_a\phi_a|\), \(x=tv^a\), \(y=t(1-v)^a\). Differentiation
under the smoothing integral is justified on compact frequency sets: all
parameter and frequency derivatives are locally bounded, and
\(v^{a_-}|\log v|\) is bounded on \((0,1)\). Conjugate symmetry then gives

\[
 u(t)\le\int_0^1\{v^au(x)f(y)+(1-v)^af(x)u(y)\}\,dv,\tag{1}
\]
\[
 w(t)\le\int_0^1\{w(x)f(y)+f(x)w(y)\}\,dv+S(t),\tag{2}
\]
\[
 S(t)\le\int_0^1\{x|\log v|u(x)f(y)
   +y|\log(1-v)|f(x)u(y)+f(x)f(y)\}\,dv.\tag{3}
\]

The last term includes the derivative of the mixing weight: \(p'=1/2\) and
\(|\phi(y)-\phi(-y)|\le2f(y)\). Omitting it would be an error.

The reviewed bootstrap supplies, uniformly on \(I\),

\[
 f(t)\le Ct^{-\beta}\quad(t\ge T_2),\qquad
 2\int_0^{1/2}f(tv^a)(1-v)^{-a\beta}\,dv\le R\quad(t\ge T),\tag{4}
\]

where we take the fixed values

\[
 T_2=6,\quad T=10,\quad \beta=8,\quad\gamma=7,
 \quad C=17/1000,\quad R=83/1000.
\]

The base certificate actually starts its tail before \(T\). Its cell proof
also bounds \(f(t)\) by \(Ct^{-\beta}\) between \(T_2\) and that tail
starting point. This is why (4) may be used on both halves of (1) and (2).

The frequency derivative has the global bound \(u\le M=2\), by Cauchy–Schwarz
and the certified second moment. Splitting (1) at one half and reflecting
gives, for a proposed bound \(u(s)\le D_1s^{-\beta}\) below \(t\),

\[
 t^\beta u(t)\le A_1+RD_1,
 \qquad A_1=\frac{MC2^{a(\beta-1)}}{a+1}.
\]

The smaller-argument integral is bounded using
\(2\int_0^{1/2}v^a(1-v)^{-a\beta}\,dv
\le2^{a(\beta-1)}/(a+1)\). The larger-argument term uses (4).
Cells check \(t^\beta u(t)<2\) on \([T_2,T]\), and the certificate checks
\(A_1<1\), so \(D_1=2\) has strict bootstrap slack.

For the parameter derivative, cells give \(w< M_a=4\) on \([0,T_2]\).
Let \(v_0=(T_2/t)^{1/a}\). Integrating the smaller-argument term in (2)
separately on \([0,v_0]\) and \([v_0,1/2]\) bounds it by

\[
 2C2^{a\beta}t^{-\beta-1/a}
 \left(M_aT_2^{1/a}+
       \frac{D_aT_2^{1/a-\gamma}}{a\gamma-1}\right).
\]

The larger-argument term contributes at most \(RD_at^{-\gamma}\), because
the corresponding half-integral with exponent \(\gamma\) is no larger than
that with exponent \(\beta\). Set

\[
 J=2C2^{a\beta}T^{\gamma-\beta-1/a},\quad
 \kappa=R+\frac{JT_2^{1/a-\gamma}}{a\gamma-1},\quad
 A_0=JM_aT_2^{1/a}.
\]

The exponent \(\gamma-\beta-1/a\) is negative, so \(t\ge T\) allows the
replacement by \(T\). The three terms of (3), using (4), are bounded by
\(A_St^{-\gamma}\), where

\[
 A_S=MC2^{a(\beta-1)}
       \left(\frac{\log2}{a+1}+\frac1{(a+1)^2}\right)
      +D_1(\log2)R+CR/T.
\]

For the first term the integral of \(v^a(-\log v)\) on \([0,1/2]\) is
evaluated exactly. For the second, \(-\log(1-v)\le\log2\). The third is
\(CRt^{-\beta}\le(CR/T)t^{-\gamma}\). Thus

\[
 t^\gamma w(t)\le A_0+A_S+\kappa D_a.
\]

The fresh certificate checks \(\kappa<1/10\), \(A_0+A_S<2\), and
\(t^\gamma w(t)<4\) on \([T_2,T]\). Since \(2+4/10<4\), it follows that
\(w(t)\le4t^{-7}\) for every \(t\ge T_2\).

Both propagations can be justified without a circular first-contact premise.
On an arbitrary compact interval \([T_2,U]\), take a maximum of the continuous
weighted derivative. If it lies in \([T_2,T]\), use the cell bound. Otherwise,
replace the candidate constant in the integral calculation by that maximum
and rearrange the strict contraction inequality. The resulting bound is
independent of \(U\). This argument is formalized by
`inhomogeneous_bootstrap` in
[TransitionBounds.lean](../../kagey-problems/problem131/lean/PaperD/Modes/TransitionBounds.lean).

The uniform bound \(t^2w(t)\le4t^{-5}\) gives dominated differentiation:

\[
 \partial_a g_a''(0)=-\frac1\pi\int_0^\infty
 t^2\Re\partial_a\phi_a(t)\,dt.
\]

The tail after \(T=10\) is at most \(1/(10000\pi)<1/30000\). On the
finite interval the actual parameter derivative is enclosed by differentiating
the parameter Taylor polynomial. Its discarded parameter terms are bounded by

\[
 \frac1\rho\sum_{i>K}i q^{i-1}
 =\frac{q^K((K+1)-Kq)}{\rho(1-q)^2},\qquad q=w_0/\rho.
\]

Here \(w_0\) is the halfwidth of \(I\), distinct from the derivative modulus
\(w(t)\). The discarded moment series is differentiated by Cauchy's estimate
on radius \(\rho-w_0\), which gives \(\tau_k(t)/(\rho-w_0)\). The
frequency-cell remainder bounds the actual high frequency derivative by the
noncancelling complex coefficient majorant. A probability-moment bound at
complex memory would be invalid and is not used.

The fourth-derivative enclosure uses the same existing Fourier majorant with
weight \(t^4\); its tail is \(CT^{-3}/3\). No parameter differentiation is
needed for it.

### Gaps

- Arb's high-precision gamma, reciprocal-gamma and power-series enclosures
  are checked by executable code with signed interval tests, but are not
  reconstructed as rational proofs inside Lean.
- The scalar inhomogeneous bootstrap and the dominated integral derivative
  are formalized. The characteristic-function differentiation and the explicit
  half-interval integration reduction above remain written analytic proofs,
  with their resulting bounds explicit in the formal interface.
- The certificate checks a neighbourhood substantially wider than the zero
  bracket. It does not claim monotonicity of central curvature on all
  \((1/2,1)\).

## What does the certificate settle?

### Takeaway

Together with the existing outside-shape theorem, strict positivity of the
parameter derivative proves a unique critical memory in the old bracket.
The fourth derivative is negative there, so the critical density belongs to
the strictly unimodal branch.

### Cited findings

- The existing strict fair-shape dichotomy is formalized in
  [RevisionShape.lean](../../kagey-problems/problem131/lean/PaperD/Modes/RevisionShape.lean).
- The old certificate proves curvature signs up to memory 0.6712 and the
  outside shape branches, using a Hankel obstruction at higher memories.
  Its data files are unchanged by this extension.
  [Existing certificate](../../kagey-problems/problem131/paperD/certify_threshold.py).
- The new sign checks and source hashes are recorded by
  [the derivative certificate](../../kagey-problems/problem131/paperD/certify_transition.py).

### Inferences

Let \(Q(a)=g_a''(0)\). Continuity and the old sign bracket supply a zero.
The positive derivative on the interior of \(I\) makes the zero unique there.
The old shape certificate settles the two branches outside the bracket.
At the zero \(a_*\), evenness gives
\(g_{a_*}'(0)=g_{a_*}'''(0)=0\), and

\[
 g_{a_*}'(x)=\frac16g_{a_*}^{(4)}(0)x^3+o(x^3)<0
 \quad\text{for small }x>0.
\]

This excludes the central-increasing branch of the dichotomy. Therefore the
fair density is strictly unimodal for \(1/2<a\le a_*\) and strictly bimodal
for \(a_*<a<1\), with the same exact bracket width as before.
No global assertion that central curvature has no additional zero in the
already bimodal region is needed: strict convexity alone would not prove it.

### Gaps

- This settles the fair-start modal transition, not the entire conjecture
  about all initial biases. The latter has a separate proof obligation.
- Square-root mode-separation asymptotics are plausible consequences of the
  same nondegeneracy, but no additional pitchfork theorem is asserted in this
  certificate. The current revision should emphasize uniqueness rather than
  grow another main-text theorem.

## How is the computation reproduced?

### Takeaway

Run the new certificate with the same `python-flint` environment as the old
threshold certificate. All acceptance checks use `require`, so optimization
flags cannot remove them.

### Cited findings

- [certify_transition.py](../../kagey-problems/problem131/paperD/certify_transition.py) runs
  a fresh base bootstrap, compact derivative cell bounds, derivative-tail
  contractions, and the final two signed enclosures. It writes source hashes,
  runtime versions, exact adopted rational bounds and all check outcomes.
- [TransitionBounds.lean](../../kagey-problems/problem131/lean/PaperD/Modes/TransitionBounds.lean)
  records the generic mathematical verification boundary.

### Inferences

The default command is

```text
python kagey-problems/problem131/paperD/certify_transition.py
```

A higher-precision reproduction is

```text
python -O kagey-problems/problem131/paperD/certify_transition.py --precision 1600 --moments 1100
```

### Gaps

The numerical source files are not substitutes for the written analytic
reduction. Both are needed to validate a computer-assisted theorem.

The final installed script passed all 19 checks at 1600-bit precision with
1100 moments under `python -O`. Its recorded source hashes match the installed
script and both unchanged reviewed helper files. It additionally rejects
nonfinite cell enclosures and empty collections. The preliminary files in this
research folder record development runs before that final hardening and are
superseded by the production record. The actual numerical output was
`[0.6890 +/- 8.16e-5]` for the memory derivative and
`[-0.07921 +/- 4.05e-6]` for the fourth spatial derivative.

The final `lake build PaperD.Modes.TransitionBounds` passed. It includes the
named `centralCurvature_deriv_pos_of_certificate` assembly, rather than only
isolated arithmetic lemmas. The formal interface still requires the explicit
Fourier derivative and numerical remainder hypotheses described above. The
written derivation is also supplied as
[or_transition_proofs.tex](../../kagey-problems/problem131/paperD/or_transition_proofs.tex).
