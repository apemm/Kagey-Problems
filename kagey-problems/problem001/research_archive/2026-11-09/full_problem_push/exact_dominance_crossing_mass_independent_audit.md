# Independent audit of the same-slope crossing masses

9 November 2026. This reviews Sections 6–8 of [exact_dominance_attempt.md](../exact_dominance_attempt.md), without changing that source. The six-cell crossing scale h log²h is correct. The proposed direction-density calculation uses the wrong transverse-scale measure, and the asserted O(log⁴h) mixed-four crossing bound is false. The corrected geometric masses still give a positive leading saving at a same-slope wall. The conditional avoidance expansion needed for an interface free energy is supplied by [central_low_collar_independent_audit.md](central_low_collar_independent_audit.md). The completed comparison, including the verified quadratic cut alignments, is reviewed in [same_slope_resolution_independent_audit.md](same_slope_resolution_independent_audit.md).

Write Lambda=1+log h. All counts below use distinct canonical positive supports, with repeated-column assignments discarded. The phase O is constant ordinary parity; C is ordinary checkerboard. A wall switches between the two opposite phases with the same slope.

## 1. A mixed-four family with crossing mass of order h

For integers k,y,t, use black cells

    (0,t), (k²+1,t), (1,y−k), (k²,y+k).

The shared white pair is (0,y),(k²+1,y). Its horizontal separation is k²+1, while the other diagonal has displacement (k²−1,2k) and the same squared length. The first two black cells and shared white pair form an axis rectangle when t≠y. Choose k in a fixed interval of size proportional to h near h/4, y near h/2 with y−k odd, and odd t≠y. All rows fit the strip, all four black rows are odd, and all four black columns are distinct.

There are Theta(h³) distinct normalized supports, each of span Theta(h²). Each has probability Theta(h^−4). Thus their crossing weight is Omega(h). These supports are minimal in the protected O phase: there are no smaller singleton or vertical rivals, and the four points do not form a hidden rectangle. The only possible equal-x-sum diagonal pairing has row sums 2t and 2y, which differ. This disproves the stated O(log⁴h) bound, even for the canonical four-cell family.

## 2. The weaker bound needed for six-cell dominance

The complete mixed-four crossing mass is nevertheless

    o(h log²h).

Here is a proof from the existing uniform fixed-arc theorem in [averaged_circle_angles.md](averaged_circle_angles.md), Section 2. No shrinking-arc estimate or angular convergence rate is needed.

For a nonhorizontal black side U=k(a,b), with a,b positive and coprime, write the connector as ell(−b,a). The other black diagonal V has norm k sqrt(a²+b²), and its endpoints in the strip require |V_y|<h. There are at most h vertical placements and h/a connector scales. The black support span is at most C(ka+kb+ell b).

The connector-span term ell b contributes O(h Lambda) after multiplication by the four-cell probability, using Equation (7) of [protected_crossing_bulk_weight.md](protected_crossing_bulk_weight.md). The kb term contributes O(Lambda⁴), since kb≤h and the unweighted mixed count is O(h³ Lambda⁴). Horizontal-side supports contribute O(h), as proved in that note. Only the ka term needs an angular restriction.

Let R_strip(k,N) count representations V of k²N with |V_y|<h. The remaining crossing weight is bounded by

    C h^−2 sum_((a,b)=1) sum_(k≤h/b) k R_strip(k,a²+b²).

Replacing R_strip by r_2 gives the old majorant

    C sum_((a,b)=1) r_2(a²+b²) log(2h/b)/b²
      ≤ C h Lambda².

Fix B. The terms b>B contribute at most C h Lambda²/B, because the fixed-coordinate primitive norm bound is uniform in b. For b≤B, the portion a≤h^0.9 is O_B(h^0.9 Lambda²), using that same fixed-coordinate bound. The portion k≤h^0.9, with arbitrary a≤h, is O_B(h^0.8 Lambda²), using

    r_2(k²N)≤r_2(N)R(k),
    sum_(k≤K) kR(k)≤C K²log(2K).

In the remaining range, ka>h^1.8. For any fixed epsilon>0 and all sufficiently large h, every permitted V therefore lies in the fixed horizontal arc set |sin theta|≤epsilon. On dyadic k intervals above h^0.9, the uniform aggregate arc theorem bounds this count by [C epsilon+o(1)] times the full-circle count. The additional weight k is comparable to the dyadic scale, so the same upper bound holds for the weighted sum. Its full-circle majorant is O(h Lambda²).

Consequently the limsup of the normalized crossing weight is at most C/B+C epsilon. First let h tend to infinity, then epsilon tend to zero and B tend to infinity. This proves the claim. Reflected near-horizontal diagonal choices are included in the circle count, rather than discarded as exceptional representations.

## 3. The first span moment and its correct parity weights

Fix a prospective common corner W at row z h. For a long horizontal side use

    S=k(u,v), T=ell(−v,u), with u much larger than v.

The span-dominant regime keeps v and ell fixed while k and u range on scales h/v and h/ell. The leading measure is therefore proportional to

    [phi(v)/v³] ell^−2.

In particular, even ell have relative weight 1/4, not 1/2. The k parity is equidistributed in its long scale range. For odd v, the coprime u values split equally between odd and even; for even v, u is odd.

Put a=sum_(v odd) phi(v)/v³ and b=sum_(v even) phi(v)/v³=a/6. Directly applying the row conditions gives these coefficients, after factoring out sum ell^−2=zeta(2):

| Phase | Pure coefficient | Wall coefficient | Ratio |
|---|---:|---:|---:|
| O | 5a/16+b/4=17a/48 | 5a/16=15a/48 | 15/17 |
| C | 9a/16+b/8=28a/48 | a/16+b/8=4a/48 | 1/7 |

For example, in O with odd v and odd u, k must be even in the pure phase and odd across the long gap, while ell must be even in both. This contributes (1/2)(1/2)(1/4)=1/16 after the u parity split. Even u instead contributes 1/4. With even v, the pure contribution is b/4 and the wall contribution vanishes. The C conditions replace the two row increments by k(u+v) and ell(u+v); the same calculation gives the second row of the table.

Let C_X denote a pure coefficient in the table. The first span moment of phase-compatible rectangles through W is

    S_X(W) = 2 zeta(2) C_X A(z) h⁴ + o(h⁴),

where

    A(z)=[(1−z)⁴+z⁴]/24 + z²(1−z)²/2.

The two triangular corner-role integrals are H_+⁴/24 and H_-⁴/24. The two intermediate roles together give H_+²H_-²/2. The factor two accounts for the reflected long-side direction. For fixed v,ell these are ordinary two-dimensional Riemann sums in k,u, with congruence conditions modulo 2v. The tails are uniformly bounded by constant multiples of sum_v phi(v)/v³ and sum_ell ell^−2, which converge. Truncating these sums before taking h to infinity justifies the asymptotic and the parity weights.

## 4. From rectangle moments to canonical six-cell crossing mass

The already proved compatible degree is

    D_X(W) = [c_X/zeta(2)] f(z) h² log²h + O(h²log h),
    f(z)=1/2+z−z², c_O=5/12, c_C=1/2.

For unordered rectangle pairs through W, the sum of their individual spans is D_X(W)S_X(W), up to the irrelevant diagonal-pair correction. Replacing this by the span of the union loses only the smaller span. To see that this loss is lower order, first fix epsilon>0. Rectangles of span greater than epsilon h² have degree at most C h²/epsilon by the first-moment bound; pairs of two such rectangles have crossing probability O_epsilon(h), after summing W. The span moment below epsilon h² is at most [g(epsilon)+o(1)]h⁴, where g(epsilon) tends to zero, by the truncated Riemann-sum description above. Pairing these with arbitrary rectangles costs at most g(epsilon) times the leading scale. Take h to infinity and then epsilon to zero. Removing W from the black union changes span by at most O(h) per pair, contributing only O(log⁴h).

The leading contribution consequently has one long rectangle and one much shorter rectangle. The latter lies on one side of the cut for all but a lower-order set of translations, so it keeps its pure degree coefficient. Only the long rectangle acquires the wall coefficient in Section 3. Thus the wall-to-pure ratios are 15/17 and 1/7, not an interval between a single-rectangle ratio and its square.

The following exclusions justify using distinct minimal six-cell supports at this scale.

* If two rectangles share another black column, designate the larger-span rectangle R first. There are O(h²) partners through W with a corner in one of R's three black columns. The excluded pair-span sum is at most C h² S(W)=O(h⁶) per W, giving only O(h) crossing probability.
* A repeated description of the same six points supplies a new mixed right triangle using two black points from each original triple in turn. In particular one uses two points from the larger-span rectangle. The perpendicular-line/Thales-circle argument again leaves O(h²) possible partners. Its weighted contribution is O(h).
* A rectangle with a repeated corner column has span at most h and degree O(h log h) through W. Pairing it with arbitrary rectangles contributes O(log h+log³h/h).
* Six supports containing an old four-support have normalized count O_eta(h^(4+eta)). Multiplication by their O(h²) span and h^−6 probability gives O_eta(h^eta), which is lower order for fixed eta<1.
* At a wall, the new two-cell vertical rivals and three-cell singleton rivals have positioned counts O(h³log h) and O(h⁴log h), respectively. The fixed-cell extension bounds M_(6,2)=O_eta(h^(3+eta)) and M_(6,3)=O_eta(h^(2+eta)) show that six supports containing these new smaller events have total crossing weight O_eta(h^eta log h). No further span factor is appropriate: these small events are already positioned at the wall.

After these exclusions, the six-cell crossing masses obey

    W_(6,X) ~ (64/45)c_X C_X h log²h,
    W_(6,wall,O)/W_(6,O) -> 15/17,
    W_(6,wall,C)/W_(6,C) -> 1/7.

Here integral_0^1 f(z)A(z) dz=1/45. The normalization uses the common-corner phase density 1/2, the factor two in S_X, and probability (2/h)^6. Odd-height alphabet differences change these six-cell weights only by a relative O(1/h).

## 5. What follows, and what does not

At the raw canonical-support mean level, a same-slope wall removes a fixed positive fraction of the leading six-cell crossing mass. Mixed and hidden four-cell crossing means are lower order. The new two/three-cell means are O(h log h), also lower order. The corrected computation therefore has the favorable sign suggested in Section 6, with different constants and a weaker valid mixed upper bound.

The geometric calculation alone does not establish an expansion for the exact wall factor: that factor conditions crossing avoidance on two internal avoidance families and introduces two/three-cell events with a different dependency structure. The subsequent [central low-collar audit](central_low_collar_independent_audit.md), Sections1–5, supplies the needed separate conditioning argument and establishes J_XY=−W_XY+o(h log²h) for the ordinary same-slope walls. Its regularly spaced construction also gives a canonical rate gain of at least c log²h over the pure ordinary-parity phases. Neither argument determines optimal wall spacing or puts every competitive recurrent component in the canonical component.

Section 7 is addressed separately by [exact_dominance_codegree_tail_audit.md](exact_dominance_codegree_tail_audit.md). Its corrected moment proof passes independent review: complete-union assignment domination gives the deleted-letter and multi-free-load tails under normalized protected avoidance. It does not give the analogous assignment domination under an arbitrary component's Perron measure. Section 8 remains conditional on that unresolved component-level bridge or an adequate alternative.
