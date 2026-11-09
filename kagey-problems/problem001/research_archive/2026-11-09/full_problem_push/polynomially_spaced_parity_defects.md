# Polynomially spaced defects preserve the protected pressure

9 November 2026. A refined diagonal-completion bound removes the large separation requirement in [dilute_parity_defects.md](dilute_parity_defects.md). The result allows an unlimited number of defects and unlimited connected-cluster size. Both the fixed-power theorem and the single subpolynomial-spacing theorem in Section 5 passed [independent review](protected_phase_pressure_independent_audit.md).

Let \(r_{\alpha}(h)\) be the entropy of valid ordinary-parity seas in which any two even-row letters have column distance at least \(\lceil h^\alpha\rceil\). For every fixed \(\alpha>0\), there is \(c_\alpha>0\) such that, for each fixed \(\varepsilon>0\),
\[
 \log r_{\alpha}(h)
 \le\log r_{\mathrm O}(h)
       +O_{\alpha,\varepsilon}(h^{-2+\varepsilon})
       +\exp[-c_\alpha\log^2h].
\tag{1}
\]
The all-odd phase is contained in this class. Thus polynomially spaced parity flips do not change its first-order pressure, even when the defect set is infinite and connected under the earlier gap-\(2L\) cluster definition.

## 1. Sharper incidence for a fixed root distance

Fix a black point P and a completion column at horizontal distance \(d>0\). Only \(d\le L=2W_h=O(h^2)\) is relevant. Let W vary over that column's rows. The sum of the numbers of eligible tilted rectangles through P,W is at most
\[
 C h^2\frac{\tau(d)}d
 +O_\eta\left(h^\eta\min(h,h^2/d)\right)
\tag{2}
\]
for every fixed \(\eta>0\). Here eligible means that all four corner columns are distinct, as in the rooted three-cell family.

For the side case, write the vertical difference as v. The count is at most \(Ch\gcd(d,v)/d\). The case \(v=0\) would give an axis rectangle and is excluded. Therefore
\[
 \sum_{0<|v|<h}\gcd(d,v)
 \le Ch\sum_{u\mid d}\frac{\varphi(u)}u
 \le Ch\tau(d),
\]
which gives the first term in (2), without the extra O(h) term in the earlier unrestricted gcd bound.

For the diagonal case, orient the alternate diagonal \((z,w)\) with \(z>0\). The four-distinct-column condition excludes \(z=0\). If the original diagonal is \((d,v)\), then
\[
 z^2+w^2=d^2+v^2,\qquad |v|,|w|<h.
\]
Set \(e=z-d\). The choice \(e=0\) gives either a degenerate rectangle or an axis rectangle, so it does not occur. Moreover
\[
 0<|e|\le h^2/d,\qquad
 (v-w)(v+w)=e(2d+e)\ne0.
\tag{3}
\]
For fixed e, the signed divisor pairs of the nonzero integer on the right determine \((v,w)\), up to constantly many choices. All integers involved have polynomial height in h, so there are \(O_\eta(h^\eta)\) choices. Summing e gives \(O_\eta(h^{2+\eta}/d)\). The direct sum over the \(O(h)\) possible v and the usual circle divisor bound also gives \(O_\eta(h^{1+\eta})\). Their minimum proves the second term of (2).

Choose the row of P in h ways and multiply by the \(O(h^{-3})\) event probability. The rooted-event incidence at a free column at distance d is consequently at most
\[
 C\frac{\tau(d)}d+\frac{C_\eta h^\eta}{\max(h,d)}.
\tag{4}
\]
For one fixed black point, the corresponding event count is h squared times this bound.

## 2. Summing over polynomially separated roots

Let \(g=\lceil h^\alpha\rceil\), and choose \(0<\eta<\min(\alpha/2,1/4)\). For a set S of roots at mutual distance at least g, fix any column x. At most two roots are closer than \(g/2\). Each of their side weights \(\tau(d)/d\) is at most one, and each diagonal weight is \(O_\eta(h^{-1+\eta})\).

The remaining distances, in increasing order, are at least a constant times \(ng\). The uniform divisor bound on \(d\le L=O(h^2)\) gives \(\tau(d)\le C_\eta h^\eta\), after decreasing its input exponent if necessary. Thus
\[
 \sum_{\substack{j\in S\\0<|j-x|\le L}}
 \left[\frac{\tau(|j-x|)}{|j-x|}
       +\frac{h^\eta}{\max(h,|j-x|)}\right]
 =O_\alpha(1).
\tag{5}
\]
The contribution of all but the two nearest roots is
\(O_\alpha(h^{\eta-\alpha}\log h)=o(1)\). When x is itself a root, every other root is at distance at least g, so the entire sum over those other roots is o(1).

## 3. Rooted mean and overlap bounds

Use the same three-cell singleton-rival events as in the dilute and cluster notes. A root initially has mean
\[
 \nu_j\sim\frac{20}{3\pi^2}\log^2h.
\]
Require its three black columns to avoid every defect. Equation (5), evaluated at the root, shows that this exclusion loses only o(1) mean per root. Therefore n roots retain total mean at least \(c_0n\log^2h\).

Equation (5) bounds the incident rooted-event probability at every free column by \(O_\alpha(1)\). It also bounds the number of rooted events through one fixed black point by \(O_\alpha(h^2)\). Since there are \(O(nh^3\log^2h)\) rooted events, compatible pairs sharing one black assignment have total joint probability \(O_\alpha(n\log^2h)\).

Pairs sharing two assignments obey the same bound, without counting the roots one by one. Two fixed black points in distinct columns place the completion W on one of constantly many perpendicular lines or Thales circles. A perpendicular line is not horizontal because the fixed columns differ; each such line has O(h) strip lattice points. A circle meets each row at most twice. Hence there are O(h) completion points in total, regardless of how many roots there are. The two-shared-cell joint sum is at most
\[
 O(nh^3\log^2h\cdot h\cdot h^{-4})
 =O(n\log^2h).
\tag{6}
\]
Three fixed black points determine their unique rectangle and completion. Conflicting assignments contribute zero.

## 4. Preserve the bulk pressure and sum profiles

Retain all ordinary minimal four/six events avoiding the n defects. Their mean is \(m\mu_{\mathrm O}(h)-O_\eta(nh^{-1+\eta})+O_h(1)\). Their bulk/bulk joint sum is \(O_\varepsilon(mh^{-2+\varepsilon})\), and their joint sum with rooted events is \(O_\eta(nh^{-1+\eta})\), by the established support-extension table.

Independently thin all rooted indicators by a sufficiently small constant \(\theta_\alpha>0\), leaving the bulk indicators unchanged. Equation (5) makes the strong-graph neighbor sum bounded. The rooted mean is linear in \(\theta_\alpha\), while the rooted/rooted joint sum is quadratic in it. The arbitrary-indicator Suen bound therefore yields
\[
 \Pr(\text{valid}\mid S)
 \le\exp[-m\mu_{\mathrm O}(h)
         -c_\alpha|S|\log^2h
         +O_{\alpha,\varepsilon}(mh^{-2+\varepsilon})+O_h(1)].
\tag{7}
\]
Roots within L of either end can be omitted, changing only the height-dependent factor.

For each profile the product space has size at most \(\lceil h/2\rceil^m\). Dropping the separation restriction enlarges the weighted profile sum to
\[
 \sum_S e^{-c_\alpha|S|\log^2h}
 \le(1+e^{-c_\alpha\log^2h})^m.
\]
Combine (7) with the protected-phase expansion to obtain (1).

The unresolved profiles have more tightly packed defects than every fixed polynomial spacing condition permits. This theorem does not bound those profiles or establish full component dominance.

## 5. One subpolynomial spacing suffices

The divisor bound can be retained explicitly instead of replacing it by \(h^\eta\). Put
\[
 M_h=\left\lceil4(L+h^2)^2\right\rceil,\qquad
 T_h=\max_{1\le n\le M_h}\tau(n),\qquad
 g_h=\left\lceil T_h(1+\log h)^2\right\rceil.
\tag{8}
\]
All norms and nonzero factorizations used in Section 1 are at most \(M_h=O(h^4)\). Therefore (4) has the uniform version
\[
 C\left[\frac{\tau(d)}d+\frac{T_h}{\max(h,d)}\right].
\tag{9}
\]
If defects are \(g_h\)-separated, at most two are near a free column. Their side contributions are at most one each, and their diagonal contributions are \(O(T_h/h)=o(1)\). The remaining roots have distances at least a constant times \(ng_h\), and their total contribution is
\[
 O\left(\frac{T_h}{g_h}\log L\right)
 =O(1/\log h)=o(1).
\tag{10}
\]
At a root, every other defect is in this latter range. Thus the incidence is bounded by an absolute constant, and the mean lost per root is o(1). Sections 3--4 apply with absolute thinning and penalty constants.

Consequently, if \(r_g(h)\) is the entropy with minimum defect spacing \(g_h\), then for some absolute \(c>0\),
\[
 \log r_g(h)\le\log r_{\mathrm O}(h)
  +O_\varepsilon(h^{-2+\varepsilon})
  +\exp[-c\log^2h].
\tag{11}
\]
This is a single spacing condition stronger than the family of fixed-power conclusions: \(g_h=h^{o(1)}\), so it is eventually smaller than \(h^\alpha\) for every fixed \(\alpha>0\).

For completeness, the elementary maximum-divisor bound gives
\[
 T_h\le \exp\left(O\left(\frac{\log h}{\log\log h}\right)\right).
\]
To see this uniformly for \(n\le M\), split its prime factors at \(y=\sqrt{\log M}\). There are at most y small primes, each with exponent at most \(O(\log M)\), contributing logarithm \(O(\sqrt{\log M}\log\log M)\) to \(\tau(n)\). The large-prime exponents have sum at most \(2\log M/\log\log M\); use \(e+1\le2^e\). This proves the displayed bound without a prime-number theorem.

In particular, some sufficiently large absolute C makes
\[
 \left\lceil\exp\left(C\frac{\log h}{\log\log h}\right)\right\rceil
\]
a sufficient minimum spacing in (11), for all sufficiently large h. Dense defect patterns remain outside the theorem.
