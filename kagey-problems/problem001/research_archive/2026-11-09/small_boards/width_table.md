# Equality widths by height

9 November 2026. W(h) is the best known width from which f(h, m) = m + floor(h^2/4) holds for every
m >= W(h). It is exact when equality is also known to fail at width W(h) - 1, so that W(h) = m_0(h).

| h | floor(h^2/4) | W(h) | Status | W(h)/h^2 | Certificate |
|---:|---:|---:|---|---:|---|
| 4 | 4 | 6 | exact | 0.375 | paper, four-row theorem; f(4,5) = 8 |
| 5 | 6 | 8 | exact | 0.320 | paper, five-row theorem; f(5,7) = 12 |
| 6 | 9 | 15 | exact | 0.417 | paper, six-row theorem; f(6,14) = 22 |
| 7 | 12 | 21 | exact (computer-assisted) | 0.429 | `seven_row_equality_width_exclusions.md`, `seven_row_equality_tail.md` |
| 8 | 16 | 39 | upper bound only; 17 <= m_0(8) <= 39 | <= 0.609 | new, `sat_h8_h9.md`; the earlier bound was 46 |
| 9 | 20 | 54 | upper bound only; 20 <= m_0(9) <= 54 | <= 0.667 | new, `sat_h8_h9.md`; the earlier bound was 58 |
| 11 | 30 | 117 | upper bound only | <= 0.967 | 11 x 169 collar board, core of 117 columns (`2026-11-07/data/cegar_h11_warm_t3.json`) |
| 15 | 56 | 441 | upper bound only | <= 1.960 | `height_fifteen_spacing_eight_completion.md` |
| 19 | 90 | 713 | upper bound only | <= 1.975 | `periodic_binary_completions_h15_h19.md` |

Only heights 4, 5, 6, 7 are exact. Everything from height 8 on is an upper bound, and the three large
ones come from dilute designs (a double in every fourth column at height 11, in every eighth column at
heights 15 and 19), so their ratios say nothing about the true size of m_0(h)/h^2.

## Notes on the rows

- **Heights 4 to 6.** The values and boards are in `jis/pemmasani_jis.tex`. The boards at widths 6, 8
  and 15 were checked again here (`verify_small.py`): the four-row family at widths 6 to 12, S_8 with 0
  to 5 extra row-1 columns, and the 6 x 15 board. As a second check, the exact encoder of this folder
  returns UNSAT for every balanced partition at widths 5, 7 and 14 and finds boards at 6, 8 and 15
  (`calibrate_encoder.json`). That check relies on the equality classification (one double per pair of a
  complete balanced bipartite row graph, singletons elsewhere).
- **Height 7.** The four 7 x 21 boards were re-verified here. The exclusion of widths 17 to 20 is the
  stored solver result and has no proof log. The paper itself states only m >= 24.
- **Height 11.** The stored board is 169 columns wide: 26 pad columns in row 1, a core of 117 columns,
  26 pad columns in row 11. Deleting pad columns and the collar theorem give every width from 117 on.
  Three more 11 x 169 boards with the same layout exist in `2026-11-07/data`.
- **Heights 15 and 19.** Widths 441 and 713 are 8 (q - 1) + 1 with q = 56 and 90. Each board has a
  checked transition to a constant row-2 tail, so equality holds at every larger width.
- **Height 9, width 77.** `constant_sea_h9_cadical195_seed18_odd57.json` holds a valid 9 x 77 equality
  board (spacing 4). It is re-verified here but is superseded by the bound 54.
- **Other heights.** I found no equality board at heights 10, 12, 13, 14, 16, 17, 18 or above 19. The
  searches at height 10 in `2026-11-07/REPORT.md` are unresolved, the spacing-8 attempts at heights 16
  and 23 in `full_problem_push` ended unknown, and no board at height 13 is stored. For these heights
  only the general threshold M_h of the paper applies (order h^4/8; M_8 = 421, M_9 = 685).

## Growth

| h | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|
| W(h) | 6 | 8 | 15 | 21 | <= 39 | <= 54 |
| W(h) / floor(h^2/4) | 1.50 | 1.33 | 1.67 | 1.75 | <= 2.44 | <= 2.70 |

The exact values use 1.3 to 1.75 columns per double. The 8 and 9 row bounds use 2.4 and 2.7, and the
searches one column below both bounds were still undecided when the time budget ended, so neither
bound is known to be sharp.
