import PaperA.AllbinAsymptotics

/-!
# Corollary `cor:boundary-layer`: the moving boundary layer

At odds `u = v_N > 0`, that is `p = 1/(1 + v_N)`, let `ℒ_N` be the number of bins
`1 ≤ k ≤ ⌊N/2⌋` with `P_N(k) < P_N(0)` (`layerCount`). If `Ω_N = 1/(√N v_N) → ∞` and
`log Ω_N/(N v_N) → 0`, then `ℒ_N ~ Ω_N² log² Ω_N` (`boundary_layer`), the total number of
interior bins below the endpoint height is `2ℒ_N` for all large `N` (`boundary_layer_total`), and
for `v_N = N^{-κ}` with `1/2 < κ < 1`, `ℒ_N ~ (κ - 1/2)² N^{2κ-1} log² N`
(`boundary_layer_power`).
-/

namespace Kagey131

open Filter Topology Asymptotics

/-- The number of bins `1 ≤ k ≤ ⌊N/2⌋` strictly below the endpoint at odds `v`. -/
noncomputable def layerCount (v : ℝ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 (N / 2)).filter
    (fun k => binProb (1 / (1 + v)) N k < binProb (1 / (1 + v)) N 0)).card

/-- At odds `v > 0`, bin `k` (with `1 ≤ k < N`) is below the endpoint iff `v < u_{k,N-k}`. -/
theorem below_iff {v : ℝ} (hv : 0 < v) {N k : ℕ} (hk : 1 ≤ k) (hkN : k < N) :
    binProb (1 / (1 + v)) N k < binProb (1 / (1 + v)) N 0 ↔ v < uab k (N - k) := by
  have hp : 0 < 1 / (1 + v) := by positivity
  have hp1 : 1 / (1 + v) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have e : k + (N - k) = N := by omega
  have h := bin_lt_endpoint_iff (a := k) (b := N - k) hk (by omega) hp hp1
  rw [e] at h
  rw [h]
  have hu := uab_pos (a := k) (b := N - k) hk (by omega)
  unfold pab
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h' <;> linarith

/-- `u_{k,N-k}` decreases in `1 ≤ k ≤ N/2`. -/
theorem uab_anti {N j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (hk : 2 * k ≤ N) :
    uab k (N - k) ≤ uab j (N - j) := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
    have h := (allbin_order_inward k (N - k) (by omega) (by omega)).1
    have e : N - k - 1 = N - (k + 1) := by omega
    rw [e] at h
    exact le_trans h.le (ih (by omega))

/-- The count is squeezed between `a` and `c - 1` when bin `a` is below the endpoint and bin `c`
is above it. -/
theorem layerCount_bounds {v : ℝ} (hv : 0 < v) {N a c : ℕ} (ha : 1 ≤ a) (hac : a ≤ c)
    (hcN : 2 * c ≤ N) (hlow : v < uab a (N - a)) (hup : uab c (N - c) < v) :
    a ≤ layerCount v N ∧ layerCount v N ≤ c - 1 := by
  constructor
  · have hsub : Finset.Icc 1 a ⊆ (Finset.Icc 1 (N / 2)).filter
        (fun k => binProb (1 / (1 + v)) N k < binProb (1 / (1 + v)) N 0) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hk.1, by omega⟩, ?_⟩
      rw [below_iff hv hk.1 (by omega)]
      exact lt_of_lt_of_le hlow (uab_anti hk.1 hk.2 (by omega))
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    unfold layerCount
    omega
  · have hsub : (Finset.Icc 1 (N / 2)).filter
        (fun k => binProb (1 / (1 + v)) N k < binProb (1 / (1 + v)) N 0) ⊆
        Finset.Icc 1 (c - 1) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      rw [Finset.mem_Icc]
      refine ⟨hk.1.1, ?_⟩
      by_contra hck
      have hck' : c ≤ k := by omega
      have hb := (below_iff hv hk.1.1 (by omega)).1 hk.2
      have := uab_anti (N := N) (by omega) hck' (by omega)
      linarith
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    unfold layerCount
    omega


/-- Every bin below the endpoint in the left half lies before an above-endpoint bin `c`. -/
theorem below_lt_of_up {v : ℝ} (hv : 0 < v) {N c k : ℕ} (hc : 1 ≤ c) (hcN : 2 * c ≤ N)
    (hup : uab c (N - c) < v) (hk : 1 ≤ k) (hkN : k ≤ N / 2)
    (hb : binProb (1 / (1 + v)) N k < binProb (1 / (1 + v)) N 0) : k < c := by
  by_contra hck
  have hck' : c ≤ k := by omega
  have h1 := (below_iff hv hk (by omega)).1 hb
  have := uab_anti (N := N) hc hck' (by omega)
  linarith

/-- The total count of interior bins below the endpoint is twice the left-half count, once an
above-endpoint bin `c` with `2c ≤ N` exists. -/
theorem total_eq_two_layer {v : ℝ} (hv : 0 < v) {N c : ℕ} (hc : 1 ≤ c) (hcN : 2 * c ≤ N)
    (hup : uab c (N - c) < v) :
    ((Finset.Icc 1 (N - 1)).filter
      (fun k => binProb (1 / (1 + v)) N k < binProb (1 / (1 + v)) N 0)).card =
      2 * layerCount v N := by
  set P := fun k => binProb (1 / (1 + v)) N k < binProb (1 / (1 + v)) N 0 with hP
  set S := (Finset.Icc 1 (N / 2)).filter P with hS
  have hSc : ∀ k ∈ S, 1 ≤ k ∧ k < c := by
    intro k hk
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk
    exact ⟨hk.1.1, below_lt_of_up hv hc hcN hup hk.1.1 hk.1.2 hk.2⟩
  have hsymm : ∀ k, k ≤ N → (P k ↔ P (N - k)) := by
    intro k hk
    simp only [hP]
    rw [binProb_symm _ N k hk]
  have hT : (Finset.Icc 1 (N - 1)).filter P = S ∪ S.image (fun k => N - k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_image, hS]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hkP⟩
      by_cases hkh : k ≤ N / 2
      · exact Or.inl ⟨⟨hk1, hkh⟩, hkP⟩
      · right
        refine ⟨N - k, ⟨⟨by omega, by omega⟩, (hsymm k (by omega)).1 hkP⟩, by omega⟩
    · rintro (⟨⟨hk1, hk2⟩, hkP⟩ | ⟨j, ⟨⟨hj1, hj2⟩, hjP⟩, rfl⟩)
      · exact ⟨⟨hk1, by omega⟩, hkP⟩
      · have hjc : j < c := (hSc j (by rw [hS, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hj1, hj2⟩, hjP⟩)).2
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        exact (hsymm j (by omega)).1 hjP
  have hdisj : Disjoint S (S.image (fun k => N - k)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨j, hj, hjk⟩ := Finset.mem_image.1 hk'
    have h1 := hSc k hk
    have h2 := hSc j hj
    omega
  have hinj : Set.InjOn (fun k => N - k) S := by
    intro j hj k hk hjk
    have h1 := hSc j hj
    have h2 := hSc k hk
    simp only at hjk
    omega
  rw [hT, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
  show S.card + S.card = 2 * S.card
  ring

/-- `v² N Ω² log² Ω = log² Ω` with `Ω = 1/(√N v)`. -/
theorem layer_identity {N v : ℝ} (hN : 0 < N) (hv : 0 < v) (ℓ : ℝ) :
    v ^ 2 * N * ((1 / (Real.sqrt N * v)) ^ 2 * ℓ ^ 2) = ℓ ^ 2 := by
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  field_simp
  rw [hs]

set_option maxHeartbeats 2000000 in
/-- The deterministic core of Corollary `cor:boundary-layer` at one `N` and one `θ ∈ (0, 1/2]`.
With `Ω = 1/(√N v)`, `ℓ = log Ω` and `d = Ω² ℓ²`, the hypotheses say that `ℓ` and `d` are large and
`d/N` small. Then `(1-θ)d - 1 ≤ ℒ_N ≤ (1+θ)d`, and bin `⌈(1+θ)d⌉` is above the endpoint. -/
theorem layer_core {θ v : ℝ} {N a₀ : ℕ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hv : 0 < v)
    (hN : 1 ≤ N)
    (hlead1 : ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      (1 - θ / 4) * Real.log a < 2 * Real.sqrt ((a : ℝ) * b) * uab a b)
    (hlead2 : ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      2 * Real.sqrt ((a : ℝ) * b) * uab a b < (1 + θ / 10) * Real.log a)
    (C1 : 4 / θ < Real.log (1 / (Real.sqrt N * v)))
    (C1' : 1 ≤ Real.log (1 / (Real.sqrt N * v)))
    (C2 : 21 / 20 * (2 * Real.log (Real.log (1 / (Real.sqrt N * v))) + 1) ≤
      θ / 5 * Real.log (1 / (Real.sqrt N * v)))
    (C3 : (a₀ : ℝ) + 1 + 4 ≤ (1 - θ) * ((1 / (Real.sqrt N * v)) ^ 2 *
      Real.log (1 / (Real.sqrt N * v)) ^ 2))
    (C4 : 8 * ((1 / (Real.sqrt N * v)) ^ 2 * Real.log (1 / (Real.sqrt N * v)) ^ 2) ≤ θ * N) :
    (1 - θ) * ((1 / (Real.sqrt N * v)) ^ 2 * Real.log (1 / (Real.sqrt N * v)) ^ 2) - 1 ≤
        layerCount v N ∧
      (layerCount v N : ℝ) ≤ (1 + θ) * ((1 / (Real.sqrt N * v)) ^ 2 *
        Real.log (1 / (Real.sqrt N * v)) ^ 2) ∧
      ∃ c : ℕ, 1 ≤ c ∧ 2 * c ≤ N ∧ uab c (N - c) < v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  generalize hΩdef : 1 / (Real.sqrt N * v) = Ω at *
  have hΩ0 : 0 < Ω := by rw [← hΩdef]; positivity
  generalize hℓdef : Real.log Ω = ℓ at *
  have hℓ0 : 0 < ℓ := by linarith
  generalize hddef : Ω ^ 2 * ℓ ^ 2 = d at *
  have hd4 : 4 ≤ d := by
    have : (0 : ℝ) ≤ a₀ := by positivity
    nlinarith
  have hid : v ^ 2 * N * d = ℓ ^ 2 := by
    rw [← hddef, ← hΩdef]; exact layer_identity hNr hv ℓ
  have hlogd : Real.log d = 2 * ℓ + 2 * Real.log ℓ := by
    rw [← hddef, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, hℓdef]
    push_cast; ring
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg C1'
  have hlog4 : Real.log 4 < 2 := by
    have h := Real.log_two_lt_d9
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  -- the two indices
  set a := ⌊(1 - θ) * d⌋₊ with ha
  set c := ⌈(1 + θ) * d⌉₊ with hc
  have hda : (1 - θ) * d - 1 < a := by
    have := Nat.lt_floor_add_one ((1 - θ) * d); linarith
  have had : (a : ℝ) ≤ (1 - θ) * d := Nat.floor_le (by nlinarith)
  have hcd : (1 + θ) * d ≤ c := Nat.le_ceil _
  have hdc : (c : ℝ) < (1 + θ) * d + 1 := Nat.ceil_lt_add_one (by nlinarith)
  have ha0 : a₀ ≤ a := by
    have : (a₀ : ℝ) < a := by linarith
    exact_mod_cast this.le
  have ha1 : 1 ≤ a := by
    have : (1 : ℝ) < a := by have : (0 : ℝ) ≤ a₀ := by positivity
                             linarith
    exact_mod_cast this.le
  have hac : a ≤ c := by
    have : (a : ℝ) ≤ c := by nlinarith
    exact_mod_cast this
  have hc2d : (c : ℝ) ≤ 2 * d := by nlinarith
  have hcN : 8 * c ≤ N := by
    have : (8 * c : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hc1 : 1 ≤ c := le_trans ha1 hac
  -- the lower index is below the endpoint
  have hNa : ((N - a : ℕ) : ℝ) = N - a := by rw [Nat.cast_sub (by omega)]
  have hlow : v < uab a (N - a) := by
    have h1 := hlead1 a (N - a) ha0 (by omega)
    have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have hb : (0 : ℝ) < ((N - a : ℕ) : ℝ) := by
      rw [hNa]
      have : (a : ℝ) < N := by exact_mod_cast (show a < N by omega)
      linarith
    have hsq : 0 < Real.sqrt ((a : ℝ) * ((N - a : ℕ) : ℝ)) := Real.sqrt_pos.2 (by positivity)
    -- `log a ≥ 2ℓ - 2`
    have hloga : 2 * ℓ - 2 ≤ Real.log a := by
      have hd4' : d / 4 ≤ a := by nlinarith
      have := Real.log_le_log (by positivity) hd4'
      rw [Real.log_div (by positivity) (by norm_num), hlogd] at this
      linarith
    -- `4 v² a (N-a) ≤ ((1-θ/4)(2ℓ-2))²`
    have hkey : 4 * v ^ 2 * ((a : ℝ) * ((N - a : ℕ) : ℝ)) ≤ ((1 - θ / 4) * (2 * ℓ - 2)) ^ 2 := by
      rw [hNa]
      have h2 : 4 * v ^ 2 * ((a : ℝ) * (N - a)) ≤ 4 * (1 - θ) * ℓ ^ 2 := by
        have : (a : ℝ) * (N - a) ≤ (1 - θ) * d * N := by nlinarith
        have hv2 : 0 ≤ 4 * v ^ 2 := by positivity
        calc 4 * v ^ 2 * ((a : ℝ) * (N - a)) ≤ 4 * v ^ 2 * ((1 - θ) * d * N) :=
              mul_le_mul_of_nonneg_left this hv2
          _ = 4 * (1 - θ) * (v ^ 2 * N * d) := by ring
          _ = 4 * (1 - θ) * ℓ ^ 2 := by rw [hid]
      have h3 : 4 * (1 - θ) * ℓ ^ 2 ≤ ((1 - θ / 4) * (2 * ℓ - 2)) ^ 2 := by
        have hθℓ : 4 < θ * ℓ := by rwa [div_lt_iff₀ hθ0, mul_comm] at C1
        nlinarith [sq_nonneg (ℓ - 1), mul_pos hθ0 hℓ0]
      linarith
    have hlhs : 2 * v * Real.sqrt ((a : ℝ) * ((N - a : ℕ) : ℝ)) ≤ (1 - θ / 4) * Real.log a := by
      have e : 2 * v * Real.sqrt ((a : ℝ) * ((N - a : ℕ) : ℝ)) =
          Real.sqrt (4 * v ^ 2 * ((a : ℝ) * ((N - a : ℕ) : ℝ))) := by
        rw [show 4 * v ^ 2 * ((a : ℝ) * ((N - a : ℕ) : ℝ)) =
            (2 * v) ^ 2 * ((a : ℝ) * ((N - a : ℕ) : ℝ)) by ring,
          Real.sqrt_mul (x := (2 * v) ^ 2) (by positivity), Real.sqrt_sq (by positivity)]
      rw [e]
      have hpos : 0 ≤ (1 - θ / 4) * (2 * ℓ - 2) := by
        apply mul_nonneg (by linarith); linarith
      calc Real.sqrt (4 * v ^ 2 * ((a : ℝ) * ((N - a : ℕ) : ℝ)))
          ≤ Real.sqrt (((1 - θ / 4) * (2 * ℓ - 2)) ^ 2) := Real.sqrt_le_sqrt hkey
        _ = (1 - θ / 4) * (2 * ℓ - 2) := Real.sqrt_sq hpos
        _ ≤ (1 - θ / 4) * Real.log a := mul_le_mul_of_nonneg_left hloga (by linarith)
    have : 2 * Real.sqrt ((a : ℝ) * ((N - a : ℕ) : ℝ)) * v <
        2 * Real.sqrt ((a : ℝ) * ((N - a : ℕ) : ℝ)) * uab a (N - a) := by linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  -- the upper index is above the endpoint
  have hNc : ((N - c : ℕ) : ℝ) = N - c := by rw [Nat.cast_sub (by omega)]
  have hup : uab c (N - c) < v := by
    have h1 := hlead2 c (N - c) (le_trans ha0 hac) (by omega)
    have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
    have hb : (0 : ℝ) < ((N - c : ℕ) : ℝ) := by
      rw [hNc]
      have : (c : ℝ) < N := by exact_mod_cast (show c < N by omega)
      linarith
    have hsq : 0 < Real.sqrt ((c : ℝ) * ((N - c : ℕ) : ℝ)) := Real.sqrt_pos.2 (by positivity)
    have hlogc : Real.log c ≤ 1 + 2 * ℓ + 2 * Real.log ℓ := by
      have := Real.log_le_log hcpos hc2d
      rw [Real.log_mul (by norm_num) (by positivity), hlogd] at this
      have := Real.log_two_lt_d9
      linarith
    have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by exact_mod_cast hc1)
    have hrhs : (1 + θ / 10) * Real.log c ≤ 2 * (1 + θ / 5) * ℓ := by
      have := mul_le_mul_of_nonneg_left hlogc (by linarith : (0 : ℝ) ≤ 1 + θ / 10)
      nlinarith
    have hkey : (2 * (1 + θ / 5) * ℓ) ^ 2 ≤ 4 * v ^ 2 * ((c : ℝ) * ((N - c : ℕ) : ℝ)) := by
      rw [hNc]
      have hNc' : (N : ℝ) * (1 - θ / 4) ≤ N - c := by nlinarith
      have h2 : 4 * (1 + θ) * (1 - θ / 4) * ℓ ^ 2 ≤ 4 * v ^ 2 * ((c : ℝ) * (N - c)) := by
        have hv2 : 0 ≤ 4 * v ^ 2 := by positivity
        have h3 : (1 + θ) * d * (N * (1 - θ / 4)) ≤ (c : ℝ) * (N - c) := by
          apply mul_le_mul hcd hNc' (by nlinarith) hcpos.le
        calc 4 * (1 + θ) * (1 - θ / 4) * ℓ ^ 2
            = 4 * v ^ 2 * ((1 + θ) * d * (N * (1 - θ / 4))) := by
              rw [← hid]; ring
          _ ≤ 4 * v ^ 2 * ((c : ℝ) * (N - c)) := mul_le_mul_of_nonneg_left h3 hv2
      have h4 : (2 * (1 + θ / 5) * ℓ) ^ 2 ≤ 4 * (1 + θ) * (1 - θ / 4) * ℓ ^ 2 := by
        have : (1 + θ / 5) ^ 2 ≤ (1 + θ) * (1 - θ / 4) := by nlinarith
        nlinarith [sq_nonneg ℓ]
      linarith
    have hlhs : (1 + θ / 10) * Real.log c ≤ 2 * v * Real.sqrt ((c : ℝ) * ((N - c : ℕ) : ℝ)) := by
      have e : 2 * v * Real.sqrt ((c : ℝ) * ((N - c : ℕ) : ℝ)) =
          Real.sqrt (4 * v ^ 2 * ((c : ℝ) * ((N - c : ℕ) : ℝ))) := by
        rw [show 4 * v ^ 2 * ((c : ℝ) * ((N - c : ℕ) : ℝ)) =
            (2 * v) ^ 2 * ((c : ℝ) * ((N - c : ℕ) : ℝ)) by ring,
          Real.sqrt_mul (x := (2 * v) ^ 2) (by positivity), Real.sqrt_sq (by positivity)]
      rw [e]
      have hpos : 0 ≤ 2 * (1 + θ / 5) * ℓ := by positivity
      calc (1 + θ / 10) * Real.log c ≤ 2 * (1 + θ / 5) * ℓ := hrhs
        _ = Real.sqrt ((2 * (1 + θ / 5) * ℓ) ^ 2) := (Real.sqrt_sq hpos).symm
        _ ≤ _ := Real.sqrt_le_sqrt hkey
    have : 2 * Real.sqrt ((c : ℝ) * ((N - c : ℕ) : ℝ)) * uab c (N - c) <
        2 * Real.sqrt ((c : ℝ) * ((N - c : ℕ) : ℝ)) * v := by linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  obtain ⟨hL1, hL2⟩ := layerCount_bounds hv ha1 hac (by omega) hlow hup
  refine ⟨?_, ?_, c, hc1, by omega, hup⟩
  · have : (a : ℝ) ≤ layerCount v N := by exact_mod_cast hL1
    linarith
  · have h1 : (layerCount v N : ℝ) ≤ ((c - 1 : ℕ) : ℝ) := by exact_mod_cast hL2
    rw [Nat.cast_sub hc1] at h1
    push_cast at h1
    linarith

/-- For each `θ ∈ (0, 1/2]`, the conclusions of `layer_core` hold for all large `N`. -/
theorem layer_eventually (v : ℕ → ℝ) (hv : ∀ᶠ N in atTop, 0 < v N)
    (hΩ : Tendsto (fun N : ℕ => 1 / (Real.sqrt N * v N)) atTop atTop)
    (hlog : Tendsto (fun N : ℕ => Real.log (1 / (Real.sqrt N * v N)) / (N * v N)) atTop (𝓝 0))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      0 < (1 / (Real.sqrt N * v N)) ^ 2 * Real.log (1 / (Real.sqrt N * v N)) ^ 2 ∧
      1 / ((1 / (Real.sqrt N * v N)) ^ 2 * Real.log (1 / (Real.sqrt N * v N)) ^ 2) < θ ∧
      (1 - θ) * ((1 / (Real.sqrt N * v N)) ^ 2 * Real.log (1 / (Real.sqrt N * v N)) ^ 2) - 1 ≤
        layerCount (v N) N ∧
      (layerCount (v N) N : ℝ) ≤ (1 + θ) * ((1 / (Real.sqrt N * v N)) ^ 2 *
        Real.log (1 / (Real.sqrt N * v N)) ^ 2) ∧
      ∃ c : ℕ, 1 ≤ c ∧ 2 * c ≤ N ∧ uab c (N - c) < v N := by
  obtain ⟨a₁, ha₁⟩ := allbin_leading (ε := θ / 4) (by positivity) (by linarith)
  obtain ⟨a₂, ha₂⟩ := allbin_leading (ε := θ / 10) (by positivity) (by linarith)
  set a₀ := max a₁ a₂
  have hlead1 : ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      (1 - θ / 4) * Real.log a < 2 * Real.sqrt ((a : ℝ) * b) * uab a b :=
    fun a b ha hab => (ha₁ a b (le_trans (le_max_left _ _) ha) hab).1
  have hlead2 : ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      2 * Real.sqrt ((a : ℝ) * b) * uab a b < (1 + θ / 10) * Real.log a :=
    fun a b ha hab => (ha₂ a b (le_trans (le_max_right _ _) ha) hab).2
  -- the scales
  have hℓ : Tendsto (fun N : ℕ => Real.log (1 / (Real.sqrt N * v N))) atTop atTop :=
    Real.tendsto_log_atTop.comp hΩ
  have hd : Tendsto (fun N : ℕ => (1 / (Real.sqrt N * v N)) ^ 2 *
      Real.log (1 / (Real.sqrt N * v N)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero |>.comp hΩ).atTop_mul_atTop₀
      (tendsto_pow_atTop two_ne_zero |>.comp hℓ)
  have hlogℓ : Tendsto (fun N : ℕ => Real.log (Real.log (1 / (Real.sqrt N * v N))) /
      Real.log (1 / (Real.sqrt N * v N))) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hℓ
  have hdN : Tendsto (fun N : ℕ => (Real.log (1 / (Real.sqrt N * v N)) / (N * v N)) ^ 2)
      atTop (𝓝 0) := by
    simpa using hlog.pow 2
  filter_upwards [hv, eventually_ge_atTop 1,
    hℓ.eventually (eventually_gt_atTop (max (7 / θ) (max (4 / θ) 1))),
    hlogℓ.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 50 by positivity)),
    hd.eventually (eventually_gt_atTop (max (2 * ((a₀ : ℝ) + 5)) (2 / θ))),
    hdN.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 8 by positivity))]
    with N hvN hN1 hℓN hlogℓN hdN' hdNN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  generalize hΩdef : 1 / (Real.sqrt N * v N) = Ω at *
  generalize hℓdef : Real.log Ω = ℓ at *
  have hℓ7 : 7 / θ < ℓ := lt_of_le_of_lt (le_max_left _ _) hℓN
  have hℓ4 : 4 / θ < ℓ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hℓN
  have hℓ1 : 1 < ℓ := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hℓN
  have hℓ0 : 0 < ℓ := by linarith
  have hda : 2 * ((a₀ : ℝ) + 5) < Ω ^ 2 * ℓ ^ 2 := lt_of_le_of_lt (le_max_left _ _) hdN'
  have hdθ : 2 / θ < Ω ^ 2 * ℓ ^ 2 := lt_of_le_of_lt (le_max_right _ _) hdN'
  have hd0 : 0 < Ω ^ 2 * ℓ ^ 2 := by
    have : (0 : ℝ) ≤ a₀ := by positivity
    linarith
  -- the conditions of `layer_core`
  have C2 : 21 / 20 * (2 * Real.log ℓ + 1) ≤ θ / 5 * ℓ := by
    have h1 : Real.log ℓ < θ / 50 * ℓ := by rwa [div_lt_iff₀ hℓ0] at hlogℓN
    have h2 : 7 < θ * ℓ := by rwa [div_lt_iff₀ hθ0, mul_comm] at hℓ7
    nlinarith
  have C3 : (a₀ : ℝ) + 1 + 4 ≤ (1 - θ) * (Ω ^ 2 * ℓ ^ 2) := by nlinarith
  have hid : (Ω ^ 2 * ℓ ^ 2) / N = (ℓ / (N * v N)) ^ 2 := by
    rw [← hΩdef]
    have hv0 : 0 < v N := hvN
    have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNr.le
    field_simp
    rw [hsq]
  have C4 : 8 * (Ω ^ 2 * ℓ ^ 2) ≤ θ * N := by
    rw [← hid] at hdNN
    rw [div_lt_iff₀ hNr] at hdNN
    linarith
  have hcore := layer_core (v := v N) (N := N) hθ0 hθ hvN hN1 hlead1 hlead2
    (by rw [hΩdef, hℓdef]; exact hℓ4) (by rw [hΩdef, hℓdef]; exact hℓ1.le)
    (by rw [hΩdef, hℓdef]; exact C2) (by rw [hΩdef, hℓdef]; exact C3)
    (by rw [hΩdef, hℓdef]; exact C4)
  rw [hΩdef, hℓdef] at hcore
  obtain ⟨h1, h2, h3⟩ := hcore
  refine ⟨hd0, ?_, h1, h2, h3⟩
  rw [div_lt_iff₀ hd0]
  rw [div_lt_iff₀ hθ0] at hdθ
  linarith

/-- Corollary `cor:boundary-layer`: if `Ω_N = 1/(√N v_N) → ∞` and `log Ω_N/(N v_N) → 0`, then
`ℒ_N ~ Ω_N² log² Ω_N`. -/
theorem boundary_layer (v : ℕ → ℝ) (hv : ∀ᶠ N in atTop, 0 < v N)
    (hΩ : Tendsto (fun N : ℕ => 1 / (Real.sqrt N * v N)) atTop atTop)
    (hlog : Tendsto (fun N : ℕ => Real.log (1 / (Real.sqrt N * v N)) / (N * v N)) atTop (𝓝 0)) :
    (fun N : ℕ => (layerCount (v N) N : ℝ)) ~[atTop]
      (fun N : ℕ => (1 / (Real.sqrt N * v N)) ^ 2 * Real.log (1 / (Real.sqrt N * v N)) ^ 2) := by
  apply isEquivalent_of_tendsto_one
  rw [Metric.tendsto_nhds]
  intro ε hε
  set θ := min (ε / 3) (1 / 2) with hθdef
  have hθ0 : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθ : θ ≤ 1 / 2 := min_le_right _ _
  have hθε : θ ≤ ε / 3 := min_le_left _ _
  filter_upwards [layer_eventually v hv hΩ hlog hθ0 hθ] with N hN
  obtain ⟨hd0, hdθ, hlo, hhi, -⟩ := hN
  simp only [Pi.div_apply]
  generalize ((1 / (Real.sqrt N * v N)) ^ 2 * Real.log (1 / (Real.sqrt N * v N)) ^ 2) = d at *
  rw [Real.dist_eq, abs_lt]
  have e1 : (layerCount (v N) N : ℝ) / d - 1 = ((layerCount (v N) N : ℝ) - d) / d := by
    field_simp
  rw [e1]
  constructor
  · rw [lt_div_iff₀ hd0]
    have : 1 < θ * d := by rwa [div_lt_iff₀ hd0] at hdθ
    nlinarith
  · rw [div_lt_iff₀ hd0]
    nlinarith

/-- By symmetry the number of interior bins strictly below the endpoint is eventually `2ℒ_N`. -/
theorem boundary_layer_total (v : ℕ → ℝ) (hv : ∀ᶠ N in atTop, 0 < v N)
    (hΩ : Tendsto (fun N : ℕ => 1 / (Real.sqrt N * v N)) atTop atTop)
    (hlog : Tendsto (fun N : ℕ => Real.log (1 / (Real.sqrt N * v N)) / (N * v N)) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 (N - 1)).filter (fun k =>
        binProb (1 / (1 + v N)) N k < binProb (1 / (1 + v N)) N 0)).card =
        2 * layerCount (v N) N := by
  filter_upwards [layer_eventually v hv hΩ hlog (θ := 1 / 2) (by norm_num) le_rfl, hv]
    with N hN hvN
  obtain ⟨-, -, -, -, c, hc1, hcN, hup⟩ := hN
  exact total_eq_two_layer hvN hc1 hcN hup

/-- Corollary `cor:boundary-layer` for `v_N = N^{-κ}` with `1/2 < κ < 1`:
`ℒ_N ~ (κ - 1/2)² N^{2κ-1} log² N`. -/
theorem boundary_layer_power {κ : ℝ} (hκ1 : 1 / 2 < κ) (hκ2 : κ < 1) :
    (fun N : ℕ => (layerCount ((N : ℝ) ^ (-κ)) N : ℝ)) ~[atTop]
      (fun N : ℕ => (κ - 1 / 2) ^ 2 * (N : ℝ) ^ (2 * κ - 1) * Real.log N ^ 2) := by
  have hΩeq : ∀ N : ℕ, 1 ≤ N →
      1 / (Real.sqrt N * (N : ℝ) ^ (-κ)) = (N : ℝ) ^ (κ - 1 / 2) := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNr, one_div, ← Real.rpow_neg hNr.le]
    congr 1; ring
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) ^ (-κ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hΩ : Tendsto (fun N : ℕ => 1 / (Real.sqrt N * (N : ℝ) ^ (-κ))) atTop atTop := by
    have h := (tendsto_rpow_atTop (show 0 < κ - 1 / 2 by linarith)).comp
      tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hΩeq N hN).symm
  have hlog : Tendsto (fun N : ℕ => Real.log (1 / (Real.sqrt N * (N : ℝ) ^ (-κ))) /
      (N * (N : ℝ) ^ (-κ))) atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_atTop (show 0 < 1 - κ by linarith)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (κ - 1 / 2)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    simp only [Function.comp]
    rw [hΩeq N hN, Real.log_rpow hNr]
    have e : (N : ℝ) * (N : ℝ) ^ (-κ) = (N : ℝ) ^ (1 - κ) := by
      rw [sub_eq_add_neg, Real.rpow_add hNr, Real.rpow_one]
    rw [e]
    ring
  have h := boundary_layer (fun N : ℕ => (N : ℝ) ^ (-κ)) hpos hΩ hlog
  refine h.congr_right ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [hΩeq N hN, Real.log_rpow hNr, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
  push_cast
  rw [show (κ - 1 / 2) * 2 = 2 * κ - 1 by ring]
  ring

#print axioms layerCount_bounds
#print axioms total_eq_two_layer
#print axioms layer_core
#print axioms boundary_layer
#print axioms boundary_layer_total
#print axioms boundary_layer_power

end Kagey131
