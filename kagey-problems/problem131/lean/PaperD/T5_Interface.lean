import PaperD.T5_Checker

/-!
# Paper D, track T5: the interface names proposed in review note 06

Note 06 of the review (`06_Lean_priorities.md`, target 3) proposes the names
`interval_law_contains_ewBin`, `crossing_bracket_of_signs` and `center_min_of_certificate`.
They are restatements of `rows_sound`, `crossing_mem_of_bracket` and `centerUniqueMin_of_check`.
-/

namespace Kagey131.PaperD.T5

open Kagey131.PaperD Set

/-- The interval law contains the actual law: for every `ε ∈ [pl/q, ph/q] ⊆ [0, 1/2]`, every
`t` and every index `a`, `lo ≤ S · P(A_t = a) ≤ hi` for the computed enclosure. -/
theorem interval_law_contains_ewBin {S q pl ph : ℕ} (hS : 0 < S) (hq : 0 < q)
    (hpl : 2 * pl ≤ q) (hph : 2 * ph ≤ q) {ε : ℝ} (hlo : (pl : ℝ) / q ≤ ε)
    (hhi : ε ≤ (ph : ℝ) / q) (t a : ℕ) :
    (loOf (rows S q pl ph t) a : ℝ) ≤ S * ewBin ε t a ∧
      S * ewBin ε t a ≤ (hiOf (rows S q pl ph t) a : ℝ) :=
  ⟨lo_le (rows_sound hS hq hpl hph hlo hhi t) a, le_hi (rows_sound hS hq hpl hph hlo hhi t) a⟩

/-- The crossing bracket from checked endpoint signs. -/
theorem crossing_bracket_of_signs {S q pl ph N k : ℕ} (hS : 0 < S) (hq : 0 < q) (hpl0 : 0 < pl)
    (hplph : pl ≤ ph) (hph : 2 * ph < q) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (hb : bracketOK S q pl ph N k = true) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hc : ewBin ε N k = ewBin ε N N) : (pl : ℝ) / q < ε ∧ ε < (ph : ℝ) / q :=
  crossing_mem_of_bracket hS hq hpl0 hplph hph hk1 hkN hb h0 h1 hc

/-- The center is the unique least interior bin at the crossing, from a certificate. -/
theorem center_min_of_certificate {S q pl ph b₀ N : ℕ} (hc : checkCenter S q pl ph b₀ N = true) :
    CenterUniqueMin N :=
  centerUniqueMin_of_check hc

end Kagey131.PaperD.T5
