# Independent audit of protected domains with dilute packets

9 November 2026. [domains_with_dilute_packets.md](domains_with_dilute_packets.md) passes review. It removes the total-error-density restriction within the stated relatively dilute packet class; it does not allow arbitrary phase profiles.

Disjoint packet expansions imply total packet width O(H_h/g_h)=O(h/Λ³) near each wall. Counting all assigned guard-error subsets in an interval of length O(H_h) costs exp(o(h)) per wall. This counts actual error sets; no enumeration of their many possible guard-packet decompositions is needed. Overlapping wall neighborhoods only create harmless overcounting.

For active packets, the common primitive cutoff R*=floor(U_h/C₁) gives span at most H_h/2 and minimum horizontal leg much larger than every packet buffer. The packet is farther than H_h from all walls, so its retained geometries lie in one protected domain. Fixing any corner row fixes the vertical translate of a shape; therefore deleting the changed row set E removes only O(r/h) of this aggregate mean. The fixed-completion-row deletion estimate from the adaptive row proof is not needed here.

The three event families have the required mixed conditional bounds. Row-root completions lie in E; wall and packet completions avoid E. Packet completions lie at error columns, whereas retained wall completions avoid them. Thus distinct families cannot share all three black assignments. Fixed small marking rates control wall and packet two-cell extensions, and the existing one-cell kernel bounds are uniform for a prescribed point from any family.

The adaptive row endpoint cost C√(rh) per domain is absorbed by the actual wall mean after choosing δ₀ small. Guard-error losses are o(h) per wall. Active packet means grow like Q_h=log²U_h per error column and absorb the bounded row-root deletion cost there. The resulting absolute count has simultaneous losses aP_h(r)m, chJ, and cQ_h times the active error count.

Guard descriptions are paid by the wall term. Active packet activities sum to exp(−cQ_h), since Q_h dominates log h. Domain descriptions cost exp(−ch) in pressure. This proves the displayed absolute pressure bound and the O(log²h) residual row-distance consequence against the protected reference. Relative packet dilution, width caps, and the minimum protected-domain length remain necessary hypotheses of this argument.

## Leading protected pressure

The later [protected_domain_leading_pressure.md](protected_domain_leading_pressure.md) also passes review. It proves equality with the best protected pressure up to o(log⁴h/h) for this specified domain-and-packet language.

Restricting both primitive coordinates of a rectangle to h^(1−δ) loses O(δh²log²h+h²log h) degree at each completion row. Pairing with the full degree gives the asserted six-event mean loss. For mixed events, the audited balanced/horizontal reductions and short-scale truncation remove only O(δ²log⁴h/h)+o(log⁴h/h). The remaining vertical configurations have b≤h^(1−δ), a≤b, and connector span at most h b/a≤h^(2−δ). Restriction to original minimal supports avoids introducing redundant events into the overlap estimate.

Suen's upper bound is applied to the retained within-domain bulk first, preserving the coefficient one on its mean. The conditional lower-probability argument is then applied only to marked packet roots. Its compatible extension bounds hold for this bulk subfamily. Active packet penalties absorb the deleted bulk at active errors, and guard errors have total size O(hJ/log³h).

At wall density at most A log⁴h/h², the truncated cut loss is O(h^(−1−δ)log⁸h), the guard deletion is O(J log h), and guard-description entropy and period-boundary errors are all lower order than m log⁴h/h. The high-wall bound uses only the absolute marked wall and packet families; the earlier joint argument remains valid with E empty and the row-root family omitted. Its wall loss dominates location entropy and the protected deficit after choosing A large.

The limit order is essential and is stated correctly: fix δ>0, let h tend to infinity, and only then let δ tend to zero. This yields a leading-pressure comparison for long protected domains and relatively dilute packets. It leaves unrestricted dense phase errors, full component dominance, and the exact interface free-energy sign unresolved.
