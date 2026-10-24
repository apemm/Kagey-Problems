# Paper F audit 02: bulk Steps 5 and 6, Lemma lem:profile, Lemma lem:profile-formula

Scope: `paperF/sec_setting.tex` (scales, Lemma lem:profile and proof, fresh-plus identity) and all of
`paperF/sec_bulk.tex`, with Steps 5 and 6 and the deduction of Theorem thm:bulk (b), (c) in focus.
Read-only audit; no file in `paperF/` was changed.

## Summary

I found no false statement and no missing argument that affects the conclusion. Every step I was
asked to check closes. The items below are wording or presentation issues, ranked by severity. None
of them needs a new argument.

## Ranked list of gaps (most severe first)

1. **Minor, presentation (Step 5, "three regimes" paragraph, lines 580-583).** The text says that in
   the comparable regime "both kernels are resolved by their local limits, and the sum over m is the
   Riemann sum of the symmetric form ... with the Jacobian s/(theta_+ theta_-)". The proof does not
   do this. It resolves only the dominant factor by its local limit, at (eq:bulk-dominant). It then
   passes the other factor through Lemma lem:index(b). That is a Riemann sum in the variable y of the
   sign with the smaller scale, with mesh mu_taubar/a_taubar(k_taubar/mu_taubar) and O(K b_{taubar,N})
   points, not O(K B_N). The two descriptions agree after the substitution that gives the symmetric
   form, and I checked that substitution independently (see below). As written, though, the paragraph
   reads like a second proof that is never carried out. Fix: say "is equivalent, after the
   substitution following Lemma lem:profile-formula, to the Riemann sum of the symmetric form". The
   proof's route is in fact better than a two-sided Riemann sum. A two-sided sum has per-term errors
   o(1)/(B_N^2 theta_+ theta_-), so it would need theta_taubar bounded below. The proof's route does
   not.

2. **Minor, inconsistency (outline item 6, line 381, and Step 6, lines 604-605, against the closing
   remark, lines 632-634).** Item 6 says that the error terms depend on theta_N "only through moduli
   that are uniform on the compact set of Lemma lem:profile". Step 6 says that the slope of
   zeta_{N,x} is bounded "uniformly on the compact set ... of Lemma lem:profile". The slope is
   (mu_tau/mu_taubar) theta_{taubar,N} <= mu_max/mu_min, and that uses only theta <= 1. No
   compactness enters. The closing remark then says, correctly, that Lemma lem:profile entered only in
   part (c). Fix: drop the appeal to the compact set in item 6 and in Step 6, or say "since
   theta <= 1".

3. **Minor, wording (after Lemma lem:profile-formula, line 355).** "When theta_{taubar,N}=0 the
   formula reads ...". For finite N, theta_{sigma,N} lies in (0,1] by (eq:scales), so this case never
   occurs. The sentence is about h_theta at a boundary point of Theta, or about the limit of h_N.
   Fix: "In the limit theta_{taubar,N} -> 0 ..." or "For theta on the boundary of Theta ...".

4. **Minor, implicit standard fact (Step 5, lines 526-531).** The text states the uniformities
   a_taubar(k_taubar/mu_taubar) = b_{taubar,N}(1+o(1)) and a_tau(m) = B_N(1+o(1)), uniformly in
   m in I and |x| <= L. They come from the sequential fact quoted at lines 42-46 ("x_N/y_N -> 1
   implies f(x_N)/f(y_N) -> 1"). Passing from the sequential fact to the uniform statement is the
   usual worst-case-sequence argument (or the uniform convergence theorem, BGT Thm 1.5.2). It is
   standard but not stated. Since tau depends on N, it also helps to say that the statement is
   applied to each of the two signs separately and then maximized. Fix: add a half sentence.

5. **Cosmetic (Step 6, line 606).** The word "Equivalently" presents the subsequence remark as
   equivalent to the direct argument. It is a consequence of it, and the direct argument does not use
   it. Fix: "In particular" or "Alternatively".

No gap of type "false" or "missing hypothesis" was found.

## Step-by-step verdicts

### Lemma lem:profile (sec_setting.tex, lines 109-240)

- **Step 1 (common bound): verified.** For c >= 0 the principal branch gives
  (-ict)^a = c^a(-it)^a, and E e^{it(-p theta_- Z_-)} = exp(K (p theta_-)^a (it)^a). Both real parts
  equal |t|^a cos(pi a/2) < 0. If theta_sigma = 1, then
  |phi_theta(t)| <= exp(-c_sigma w_sigma^{a_sigma}|t|^{a_sigma}) <= exp(-c|t|^{a_*}) for |t| >= 1,
  with w_+ = 1-p and w_- = p. So c = min(c_+(1-p)^{a_+}, c_- p^{a_-}) is correct, and dropping the
  other factor (which has modulus at most 1) is legitimate.
- **Step 2 (uniform sup and Lipschitz bounds, C_0): verified.** The integrability of Phi and
  |t|Phi gives both bounds with constants that do not depend on theta. Riemann-Lebesgue applies
  because phi_theta is in L^1.
- **Step 3 (continuity of theta -> h_theta into C_0): verified.** For each t, the map
  theta -> phi_theta(t) is continuous on [0,1]^2, including at theta_sigma = 0 since a_sigma > 0. The
  integrand is dominated by 2 Phi, and the sup-norm bound by the L^1 distance of the characteristic
  functions is correct.
- **Step 4 (positivity): verified.** The scaling phi^n(t) = phi(n^{1/a}t) holds because
  K(-i n^{1/a} t)^a = n K(-it)^a. The SLLN argument against Z >= 0 is correct: a.s. divergence
  contradicts tightness of an identically distributed sequence. The induction for
  g^{*n}(y_1+...+y_n) > 0 is correct because each g^{*(n-1)} is continuous and the integrand is
  positive and continuous at one point. The identification g^{*n} = n^{-1/a} g(n^{-1/a} .) holds
  because two continuous densities of one law are equal. In the chaining, c_n = n^{1-1/a} increases
  to infinity and c_{n+1}/c_n -> 1 < (a+eps)/(a-eps), so the intervals c_n I overlap in turn and fill
  a half line. Two half lines and (U-scaling) with n = 2 give 2^{-1/a}R = R inside U. Positivity of
  h_theta follows by conditioning on the coordinate with theta_sigma = 1, whose coefficient (1-p or
  -p) is nonzero because 0 < p < 1.
- **Conclusion (compactness, inf H_N > 0, uniform lower bound on [-K,K]): verified.** The maps
  theta -> sup h_theta and theta -> min_{[-K,K]} h_theta are 1-Lipschitz for the sup norm and hence
  continuous on the compact set Theta. Each is positive, so each attains a positive minimum, and that
  minimum bounds h_{theta_N} for every N because theta_N lies in Theta.

### Lemma lem:profile-formula (sec_bulk.tex, lines 328-368)

- **Formula (eq:bulk-profile): verified** for both choices of tau. For tau = +, conditioning on
  Z_- = y gives (1-p)^{-1} g_+((x + p theta_- y)/(1-p)), and 1-p = mu_-/s, p/(1-p) = mu_+/mu_-. For
  tau = -, conditioning on Z_+ = y gives p^{-1} g_-((-x + (1-p) theta_+ y)/p) =
  (s/mu_+) g_-(-sx/mu_+ + (mu_-/mu_+) theta_+ y). This matches epsilon_- = -1.
- **Uniform bound H-bar: verified** (prefactor s/mu_taubar, ||g_tau||, and integral of g_taubar
  equal to 1).
- **Tail decay epsilon_h(R): verified.** On |y| <= sR/(2 mu_tau), the argument has modulus at least
  sR/mu_taubar - sR/(2 mu_taubar), and g-bar is nonincreasing, so the bound with sR/(2 mu_max) is
  valid. The outer part is bounded by ||g|| P(|Z| > sR/(2 mu_max)). Neither part depends on N.
- **Symmetric form and Jacobian: verified independently** (see below).

### Step 5 (lines 522-595)

- **Shift identity (eq:bulk-shift): verified** by direct expansion for tau = +, and in the same way
  for tau = -.
- **Decomposition of z_m with r_1, r_2 -> 1: verified.** The distance bound
  (sL/mu_min)|r_1-1| + (mu_max K/mu_min)|r_2-1| uses only theta_taubar <= 1. Since r_1 and r_2 involve
  one sign at a time, their rates do not depend on theta_N (apart from item 4 above).
- **(eq:bulk-dominant): verified.** The kernel local limit of Lemma lem:kernels is centred at m mu
  for all three kernels, including q_{m+1}, as its proof states. The index m is at least
  eps N/(2 mu_max) on I, so delta(m) -> 0 uniformly.
- **psi_{N,x} in Psi(omega): verified.** The slope is at most mu_max/mu_min, omega_g is
  nondecreasing, and |psi| <= 1.
- **Summing over I, adding back m not in I, then Lemma lem:index(b): verified.** The o(1) terms
  sum to o(1) by (K1). Adding back costs c_{V^tau} ||g_tau|| (eta(K)+o(1)). Lemma lem:index(b) is
  uniform over Psi(omega) and over j >= eps N, and its y_m is the same variable as in Step 5.
- **Weights (eq:bulk-weights) and identification with h_N: verified.** For sigma_0 = + the pairs
  are (q^+_{m+1}, u^-_m) with weight mu_+ * 1 and (u^+_m, q^-_m) with weight 1 * mu_-. For
  sigma_0 = - they are (u^+_m, q^-_{m+1}) with weight 1 * mu_- and (q^+_m, u^-_m) with weight
  mu_+ * 1. Each sum is s, and s/mu_taubar times the integral is exactly (eq:bulk-profile). There is
  no limit in theta.
- **Constant C_5 and the conclusion of (eq:bulk-central): verified.**
- **Pinned regimes: verified.** Plus-dominant: the weights are mu_+ (1/mu_-) + 1 * 1 = s/mu_- for
  sigma_0 = +, and 1 * (sum of q^-_{m+1} = 1 - T_-(k_-) -> 1) + mu_+ (1/mu_-) = s/mu_- for
  sigma_0 = -. The limit is (s/mu_-) g_+(sx/mu_-). Minus-dominant: (s/mu_+) g_-(-sx/mu_+), which is
  the density of -p Z_-. The statement that the first product for sigma_0 = - carries total mass
  tending to 1, not 1/mu_-, is correct.
- **"Number of terms O_K(B_N)": not literally what the text does.** See item 1. The actual count is
  O(K b_{taubar,N}), inside the proof of Lemma lem:index(b), with per-term error o(1)/a(j/mu). The
  total is o(1)(2K/mu + 1/a) -> 0. Correct.

### Step 6 (lines 597-609)

- **Verified.** The dominant sign is chosen per N. Every error term (e_{sigma,N}, delta(m),
  eta(K), the convergence in Lemma lem:index(b) over Psi(omega), epsilon_h, r_1, r_2, and the
  constants in (eq:bulk-factor) and (eq:bulk-ratios)) is a maximum over the two signs of a quantity
  that does not involve theta_N. Step 5 identifies the main term with h_N(x) exactly, not with a
  limit profile. So the bound holds uniformly in N for every sequence theta_N, oscillating ratios
  included, and no subsequence argument is needed. The only blemish is the unnecessary appeal to
  compactness (item 2).

### Deduction of Theorem thm:bulk (b) and (c) (lines 622-629)

- **(b) verified.** For N >= N_4, (a) and H-bar give B_N F <= H-bar + 1. For N < N_4,
  B_N F <= B_N <= B_{N_4}, since F <= 1 and B_N is nondecreasing (a_sigma is increasing).
- **(c) verified.** Lemma lem:profile gives c_K > 0 with h_N >= c_K on [-K,K] for all N, and then
  |B_N F/h_N - 1| <= D_N/c_K -> 0.

I also spot-checked Steps 1 to 4, since Step 5 depends on them. The constants eps, N_1, N_2(K) and
N_3, the window (eq:bulk-window), the ratio limits in (eq:bulk-ratios), the choice of K(R) and the
bound by kappa R in Step 4, and the end-of-row bound in Step 2 (8 m mu_+ < N/2 because
eps <= 1/(16 mu_+)) all check out.

## Independent derivations

**Comparable scales (Riemann sum and Jacobian).** Approximate both kernels by their local limits:
V^+_m(k) ~ c_+ g_+((k - m mu_+)/b_+)/b_+ and V^-_m(l) ~ c_- g_-((l - m mu_-)/b_-)/b_-. Put
m = N/s + t B_N and k = pN + x B_N. Then k - m mu_+ = B_N(x - mu_+ t) and
l - m mu_- = (1-p)N - xB_N - mu_- N/s - mu_- t B_N = B_N(-x - mu_- t). Summing over m (dm = B_N dt)
and multiplying by B_N gives

  B_N F ~ (sum of c_+ c_-)/(theta_+ theta_-) * integral of g_+((x - mu_+ t)/theta_+) g_-((-x - mu_- t)/theta_-) dt,

and the sum of c_+ c_- is s. As a check, the map (x,t) -> (u,v) = (x - mu_+ t, -x - mu_- t) has
|det| = mu_- + mu_+ = s, and x = (mu_- u - mu_+ v)/s = (1-p)u - p v. So the right side is the
density of (1-p) theta_+ Z_+ - p theta_- Z_-, that is h_N(x), and s/(theta_+ theta_-) is the Jacobian
of (x,t) -> (u/theta_+, v/theta_-). This agrees with the symmetric form after Lemma
lem:profile-formula. The substitution y = (-x - mu_- t)/theta_- also turns it back into
(eq:bulk-profile) when theta_+ = 1, and I checked that too.

**Plus-dominant pinned value.** If theta_- -> 0, the minus factor concentrates on m within O(b_-)
of l/mu_-, a window that is o(B_N). There, k - m mu_+ = k - (l/mu_-) mu_+ + O(b_-) = s(k - pN)/mu_- +
o(B_N) = s x B_N/mu_- + o(B_N). So B_N V^+_m(k) -> c_+ g_+(sx/mu_-), and the sum of the minus factors
tends to c_-/mu_-. The result is (sum of c_+ c_-/mu_-) g_+(sx/mu_-) = (s/mu_-) g_+(sx/mu_-). This
agrees with the text and with (eq:bulk-profile) at theta_- = 0.

## Numerical check

Script: `scripts/bulk/bulk_check.py` (this folder)
(and `compare_pinned.py` in the same folder), run with `py -I`. The recursion is a verbatim copy of
`occupation()` from `certify_atlas.py` with separate plus and minus laws. The run laws are zeta laws
with alpha_+ = 1.5 and alpha_- = 1.7, so mu_+ = 1.94737, mu_- = 1.61214, s = 3.55951 and
p = 0.54709. The start is a fresh plus start. h_N is computed by Fourier inversion of
phi_theta (scipy quad). Its total mass over [-60,60] is 0.9992, consistent with the heavy right tail.
I used two choices of a_sigma: the asymptotic power (t/(alpha zeta(alpha+1)))^{1/alpha}, and the exact
inverse of the Hurwitz tail. The row mass is 1 to 12 digits at every N.

Center bin k0 = round(pN), asymptotic scales:

| N    | theta_- | B_N P_N(k0) | h_N(x0) | ratio  | gap    | sup gap, abs(x) <= 3 |
|------|---------|-------------|---------|--------|--------|----------------------|
| 1000 | 0.650   | 0.25802     | 0.21981 | 1.1738 | 0.0382 | 0.0497               |
| 2000 | 0.616   | 0.25348     | 0.22349 | 1.1342 | 0.0300 | 0.0410               |
| 4000 | 0.583   | 0.25031     | 0.22679 | 1.1037 | 0.0235 | 0.0339               |
| 8000 | 0.552   | 0.24737     | 0.22918 | 1.0794 | 0.0182 | 0.0281               |

The exact-inverse scales give ratios 1.199, 1.150, 1.113 and 1.085. The gap at the centre shrinks by
a factor of about 0.78 per doubling, roughly like N^{-0.36}. That fits a first-order correction of
size a_+(N)/N ~ N^{-1/3}. The ratio is tending to 1, slowly, as the theorem predicts.

Moving profile against the pinned limit. Because theta_- ~ N^{1/1.7 - 1/1.5} = N^{-0.078}, the
pinned regime is far away at these N. Over abs(x) <= 4:

| N    | sup abs(B_N P - h_N) | sup abs(B_N P - h_pinned) | mean abs(B_N P - h_N) | mean abs(B_N P - h_pinned) |
|------|----------------------|---------------------------|-----------------------|----------------------------|
| 1000 | 0.0497               | 0.0970                    | 0.0169                | 0.0302                     |
| 2000 | 0.0410               | 0.0938                    | 0.0138                | 0.0288                     |
| 4000 | 0.0339               | 0.0906                    | 0.0115                | 0.0280                     |

The moving profile h_N fits about twice as well, and its error decays. The error against the pinned
profile hardly moves. This supports the paper's choice to state the theorem with h_N rather than
with its limit. (At the single centre bin the pinned value happens to be slightly closer at N = 8000.
That says nothing either way, because both differences tend to zero.)

## Verdict

- **Lemma lem:profile: sound.**
- **Lemma lem:profile-formula: sound.**
- **Step 5: sound with listed fixes** (items 1 and 4; presentation only).
- **Step 6: sound with listed fixes** (items 2 and 5; presentation only).
- **Theorem thm:bulk (b), (c): sound.**
