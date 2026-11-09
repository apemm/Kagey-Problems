# Independent audit of polylogarithmically separated packets

9 November 2026. Both [polylogarithmic_packet_separation.md](polylogarithmic_packet_separation.md) and [polylog_packets_in_protected_domains.md](polylog_packets_in_protected_domains.md) pass independent review. Their conclusions retain the stated packet separation and internal-density assumptions; they do not describe all phase words in a full recurrent component.

## The averaged diagonal kernel

Write the two diagonal vectors as (d,v) and (d+t,w), orienting the second horizontal component positively. The equal-norm equation gives (v-w)(v+w)=t(2d+t). The case t=0 is degenerate or axis-aligned and is excluded. The positivity d+t>0 ensures 2d+t>0; restricting to it only shortens the summation interval. The allowed t satisfy |t|=O(min(h,h²/D)) when d lies in [D,D+ell], ell<=D. This also holds for negative t: its magnitude is at most d, and the norm difference supplies the complementary h²/d bound.

For fixed t, the divisor hyperbola gives a bound C ell log h+C sqrt(M) for the sum of tau(2d+t), where M=max(h,D). The possible factor two in solving 2d+t modulo an even divisor is absorbed in C. Summing tau(|t|) and dividing by h² gives the stated interval kernel bound C[ell log²h/M+log h/sqrt(M)]. The two regimes D<=h and D>h have the same formula.

For a sparse annulus containing at most CD/g chosen distances, Cauchy--Schwarz and the second divisor moment give C log^(5/2)h/sqrt(g), with the additional factor sqrt(D/h) below h. Summing annuli costs at most another logarithm. Buffer columns increase the relevant density by O(log h), hence the square-root loss is only sqrt(log h). With g=log^10 h, both far incidence and buffer deletion tend to zero. All kernel sums stop at the geometric support range; using 2L for intersecting buffers is sufficient.

The far-black root family remains large uniformly up to ell=h/log³h: its primitive cutoff is at least a constant times log²h, and its retained logarithm is a fixed fraction of log(h/ell). The total two-black-point completion locus has O(h) points, so fixed-rate independent marking controls that conditional term. Bulk restoration costs O(log⁴h/h) per error, which is negligible even at the smallest retained root penalty.

The fixed-description comparison requires no density of errors inside a packet. The union count does: q>=max(1,ceil(ell/log^B h)) makes log(e ell/q) at most 1+B log log h. This is dominated by the squared logarithmic penalty. The resulting minimum of q log²(h/ell) is of order log²h over the permitted lengths, so summing all lengths preserves the claimed exponentially small activity.

## Packets inside protected domains

The guard scale H=h log^8 h exceeds every expanded packet radius h log^7 h. Disjoint expansions therefore bound the total guard width near one wall by O(h/log²h). Counting guard error sets, rather than their packet descriptions, costs exp(O(h log log h/log²h))=exp(o(h)) per wall. It is harmless that a set can receive several descriptions: the proof uses this only as an upper bound.

For an active packet, the cutoff min(h/(C A ell log h),D/(C h)) keeps every root support inside its protected domain. Its logarithm is bounded below by a constant times min(log(h/ell),log(D/h)); subtracting log log h is harmless because log(h/ell)>=3 log log h. The global upper bounds on incidence and deleted-buffer mass remain valid after restricting the cutoff.

The activity split is valid term by term: exp(-c q min(s²,t²)) is at most exp(-c q s²)+exp(-c q t²). For the second term, summing lengths and error counts gives C log^B h exp(-c' t²). Its sum over distances D>=H is bounded by h log^B h times the Gaussian logarithmic tail integral. This is o(h) per wall. The residual activity independent of wall distance is exp(-c log²h) per possible start.

The joint row, wall, and packet family has no shared three-assignment support across distinct families: their completed rows or completed columns differ by construction. The previously established compatible one- and two-assignment bounds are uniform under the new cutoff. Guard descriptions and distance-dependent activities are absorbed by the actual marked wall loss. Active packet penalties absorb the bounded per-error row loss. This verifies the row comparison with residual O(log²h) row distance.

For leading pressure at the protected row law, avoid the truncated minimal bulk first and then the marked packet roots. This retains coefficient one on the bulk mean. At low wall density, the truncated cut loss, O(J log²h) guard bulk deletion, and o(h) per-wall descriptions are all lower order than m log⁴h/h. The absolute wall bound excludes the high-density range. The order of limits is fixed truncation parameter, then h tending to infinity, then truncation parameter tending to zero.

The conclusion is equality of leading pressure with the best protected phase within this domain-and-packet language. It does not establish unrestricted component dominance.
