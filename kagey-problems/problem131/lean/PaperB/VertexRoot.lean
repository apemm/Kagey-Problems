import PaperB.VertexH

/-!
# Paper B, Theorem `thm:vertex-uniform-root`: the bracket argument

* `logH_increment`: integrating the elasticity, for `0 < s ≤ t`,
  `log H(t) - log H(s) ≥ κ(s) (log t - log s)` (monotonicity of `κ`).
* `upper_step`, `lower_step`, `log_chain`, `s_bound`: the explicit inequalities
  with `K = ℓ + √ℓ + 1` (the paper's `c_ℓ`), `ε = √((A+1)/b)`, `δ = 16Kε ≤ 1/2` (the
  "16K / 25K / 32K" arithmetic).
* `vertex_bracket`: the proof of Theorem `thm:vertex-uniform-root` assembled,
  assuming the two inequalities of Lemma `lem:vertex-randomization`
  (`eq:vertex-jensen-lower` and `eq:vertex-tangent-upper`) as hypotheses about
  the crossing polynomial `S`. Its conclusion is `S(u₊) > 1 > S(u₋)` with
  `u_± = (1 ± δ) √(y_a/b)`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial Real

variable {ℓ : ℕ}

/-- `∑_i log(y Z_i(y)) = log H(y)` for `y > 0`. -/
noncomputable def logHf (m : Fin ℓ → ℕ) (y : ℝ) : ℝ := ∑ i, Real.log (y * Zf (m i) y)

theorem logHf_eq (m : Fin ℓ → ℕ) {y : ℝ} (hy : 0 < y) :
    logHf m y = Real.log ((Hpoly m).eval y) := by
  unfold logHf Hpoly
  rw [eval_prod, Real.log_prod (fun i _ => (Bpoly_eval_pos hy _).ne')]
  exact sum_congr rfl fun i _ => by rw [Bpoly_succ_eval]

theorem logHf_hasDerivAt (m : Fin ℓ → ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (logHf m) (kapH m y / y) y := by
  unfold logHf kapH
  rw [sum_div]
  exact HasDerivAt.fun_sum fun i _ => logB_hasDerivAt hy

/-- Integrated elasticity: for `0 < s ≤ t`,
`log H(t) - log H(s) ≥ κ(s) (log t - log s)`. -/
theorem logH_increment (m : Fin ℓ → ℕ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    kapH m s * (Real.log t - Real.log s) ≤
      Real.log ((Hpoly m).eval t) - Real.log ((Hpoly m).eval s) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  rw [← logHf_eq m hs, ← logHf_eq m ht]
  set c := kapH m s
  let g : ℝ → ℝ := fun x => logHf m x - c * Real.log x
  have hd : ∀ x, 0 < x → HasDerivAt g ((kapH m x - c) / x) x := by
    intro x hx
    have := (logHf_hasDerivAt m hx).sub ((Real.hasDerivAt_log hx.ne').const_mul c)
    refine this.congr_deriv ?_
    field_simp
  have hmono : MonotoneOn g (Set.Ici s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici s)
    · exact fun x hx => (hd x (lt_of_lt_of_le hs hx)).continuousAt.continuousWithinAt
    · rw [interior_Ici]
      exact fun x hx => (hd x (hs.trans hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      have hx0 : 0 < x := hs.trans hx
      rw [(hd x hx0).deriv]
      apply div_nonneg _ hx0.le
      have := kapH_monotoneOn m (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr hx0) (le_of_lt hx)
      linarith
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hst) hst
  simp only [g] at this
  linarith

/-- Upper bracket arithmetic (`u₊ = (1+δ)u₀`). -/
theorem upper_step {L K ε δ κ0 A u0 : ℝ} (hL : 1 ≤ L) (hK : K = L + Real.sqrt L + 1)
    (hε : 0 < ε) (hδ : δ = 16 * K * ε) (hδ2 : δ ≤ 1 / 2) (hκ : 0 < κ0) (hA : 0 ≤ A)
    (hu0 : 0 < u0) (hu0ε : u0 ≤ ε) (hAu : A * u0 ≤ 2 * κ0 * ε) :
    (1 + δ) * u0 < 1 / 4 ∧
      κ0 * (4 / 3 * δ - 4 * ε) ≤ 2 * κ0 * Real.log (1 + δ) - A * ((1 + δ) * u0) / (1 - (1 + δ) * u0) ∧
      0 < κ0 * (4 / 3 * δ - 4 * ε) := by
  have hsq : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL
  have hK3 : 3 ≤ K := by rw [hK]; linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hε96 : ε ≤ 1 / 96 := by
    have : 16 * K * ε ≤ 1 / 2 := hδ ▸ hδ2
    nlinarith
  have hup : (1 + δ) * u0 ≤ 3 / 2 * ε := by nlinarith
  have hup4 : (1 + δ) * u0 < 1 / 4 := by linarith
  refine ⟨hup4, ?_, ?_⟩
  · have hlog : 2 * δ / (δ + 2) ≤ Real.log (1 + δ) := Real.le_log_one_add_of_nonneg hδ0
    have hlog' : 2 / 3 * δ ≤ Real.log (1 + δ) := by
      refine le_trans ?_ hlog
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have hpos : 0 < 1 - (1 + δ) * u0 := by linarith
    have hfrac : A * ((1 + δ) * u0) / (1 - (1 + δ) * u0) ≤ 4 * κ0 * ε := by
      rw [div_le_iff₀ hpos]
      have h1 : A * ((1 + δ) * u0) ≤ 3 / 2 * (A * u0) := by
        nlinarith [mul_le_mul_of_nonneg_left hδ2 (mul_nonneg hA hu0.le)]
      have h2 := mul_le_mul_of_nonneg_left (show (3 : ℝ) / 4 ≤ 1 - (1 + δ) * u0 by linarith)
        (show 0 ≤ 4 * κ0 * ε by positivity)
      nlinarith
    nlinarith
  · have : 48 * ε ≤ δ := by rw [hδ]; nlinarith
    apply mul_pos hκ; linarith

/-- The logarithmic chain in the lower bracket:
`-κ - 2 log(1-s) + (b-1) log(1 + us/(1-s)) ≤ -κ + 2s/(1-s) + b u s/(1-s)`. -/
theorem log_chain {κ u s b : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hs1 : s < 1) (hb : 1 ≤ b) :
    -κ - 2 * Real.log (1 - s) + (b - 1) * Real.log (1 + u * s / (1 - s)) ≤
      -κ + 2 * s / (1 - s) + b * u * s / (1 - s) := by
  have h1s : 0 < 1 - s := by linarith
  have hx : 0 ≤ u * s / (1 - s) := by positivity
  have hl1 : Real.log (1 + u * s / (1 - s)) ≤ u * s / (1 - s) := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + u * s / (1 - s)); linarith
  have hl2 : -Real.log (1 - s) ≤ s / (1 - s) := by
    have := Real.one_sub_inv_le_log_of_pos h1s
    have e : 1 - (1 - s)⁻¹ = -(s / (1 - s)) := by field_simp; ring
    linarith
  have hlpos : 0 ≤ Real.log (1 + u * s / (1 - s)) := Real.log_nonneg (by linarith)
  have : (b - 1) * Real.log (1 + u * s / (1 - s)) ≤ b * (u * s / (1 - s)) := by
    calc (b - 1) * Real.log (1 + u * s / (1 - s)) ≤ (b - 1) * (u * s / (1 - s)) :=
          mul_le_mul_of_nonneg_left hl1 (by linarith)
      _ ≤ b * (u * s / (1 - s)) := by nlinarith
  have e2 : b * u * s / (1 - s) = b * (u * s / (1 - s)) := by ring
  rw [e2]
  have e3 : 2 * s / (1 - s) = 2 * (s / (1 - s)) := by ring
  rw [e3]
  linarith

/-- The size of the tilting parameter: if `κ ≤ ℓ + √ℓ √A √b u`, `bu ≥ 1/(2ε)`,
`√A ≤ ε √b` and `u ≤ 1/2`, then `s = κ/(bu(1-u)) ≤ 2(2ℓ + √ℓ) ε`. -/
theorem s_bound {L κ A b u ε : ℝ} (hL : 0 ≤ L) (hb : 0 < b) (hu : 0 < u) (hu2 : u ≤ 1 / 2)
    (hε : 0 < ε) (hκ : κ ≤ L + Real.sqrt L * Real.sqrt A * Real.sqrt b * u)
    (hbu : 1 / (2 * ε) ≤ b * u) (hAb : Real.sqrt A ≤ ε * Real.sqrt b) :
    κ / (b * u * (1 - u)) ≤ 2 * (2 * L + Real.sqrt L) * ε := by
  have hbu0 : 0 < b * u := mul_pos hb hu
  have h1u : 1 / 2 ≤ 1 - u := by linarith
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hbsq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have hL1 : L / (b * u) ≤ 2 * L * ε := by
    rw [div_le_iff₀ hbu0]
    have : 1 ≤ 2 * ε * (b * u) := by rw [div_le_iff₀ (by positivity)] at hbu; linarith
    nlinarith
  have hL2 : Real.sqrt L * Real.sqrt A * Real.sqrt b * u / (b * u) ≤ Real.sqrt L * ε := by
    rw [div_le_iff₀ hbu0]
    have hsL := Real.sqrt_nonneg L
    calc Real.sqrt L * Real.sqrt A * Real.sqrt b * u
        ≤ Real.sqrt L * (ε * Real.sqrt b) * Real.sqrt b * u := by gcongr
      _ = Real.sqrt L * ε * (Real.sqrt b * Real.sqrt b) * u := by ring
      _ = Real.sqrt L * ε * (b * u) := by rw [hbsq]; ring
  have hκbu : κ / (b * u) ≤ (2 * L + Real.sqrt L) * ε := by
    have := div_le_div_of_nonneg_right hκ hbu0.le
    rw [add_div] at this
    linarith
  rw [show b * u * (1 - u) = (b * u) * (1 - u) by ring, ← div_div]
  rw [div_le_iff₀ (by linarith)]
  have hpos : 0 ≤ (2 * L + Real.sqrt L) * ε := by positivity
  nlinarith

/-- Lower bracket arithmetic (`u₋ = (1-δ)u₀`). -/
theorem lower_step {κ u s ε K δ : ℝ} (hκ : 1 ≤ κ) (hu : 0 ≤ u) (huε : u ≤ ε) (hs : 0 ≤ s)
    (hsK : s ≤ 4 * K * ε) (hs8 : s ≤ 1 / 8) (hu4 : u ≤ 1 / 4) (hK : 1 ≤ K) (hε : 0 < ε)
    (hδ : δ = 16 * K * ε) (hδ2 : δ ≤ 1 / 2) :
    κ * (1 / ((1 - u) * (1 - s)) - 1) + 2 * s / (1 - s) ≤ 25 * K * κ * ε ∧
      2 * κ * Real.log (1 - δ) + 25 * K * κ * ε < 0 := by
  have h1u : 3 / 4 ≤ 1 - u := by linarith
  have h1s : 7 / 8 ≤ 1 - s := by linarith
  have hprod : 21 / 32 ≤ (1 - u) * (1 - s) := by nlinarith
  constructor
  · have e : 1 / ((1 - u) * (1 - s)) - 1 = (u + s - u * s) / ((1 - u) * (1 - s)) := by
      field_simp; ring
    rw [e]
    have t1 : (u + s - u * s) / ((1 - u) * (1 - s)) ≤ 32 / 21 * (u + s) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have t2 : 2 * s / (1 - s) ≤ 16 / 7 * s := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have t3 : u + s ≤ ε + 4 * K * ε := by linarith
    have t4 : ε + 4 * K * ε ≤ 5 * K * ε := by nlinarith
    have hκ0 : 0 ≤ κ := by linarith
    have : κ * ((u + s - u * s) / ((1 - u) * (1 - s))) ≤ κ * (32 / 21 * (u + s)) :=
      mul_le_mul_of_nonneg_left t1 hκ0
    have : 16 / 7 * s ≤ κ * (16 / 7 * s) := by nlinarith
    nlinarith
  · have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
    have hlog : Real.log (1 - δ) ≤ -δ := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - δ); linarith
    have : 2 * κ * Real.log (1 - δ) ≤ -2 * κ * δ := by nlinarith
    rw [hδ] at this
    nlinarith

theorem log_one_sub_ge {x : ℝ} (hx : x < 1) : -(x / (1 - x)) ≤ Real.log (1 - x) := by
  have h := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 - x)
  have e : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by
    have : (1 - x) ≠ 0 := by linarith
    field_simp; ring
  linarith

/-- Lower bracket, abstract form: with `u₋ = (1-δ)u₀`,
`s = κ/(b u₋ (1-u₋))`, if `log H(y) ≤ 2κ log(1-δ)` then `s < 1/8` and
`log H(y) - κ - 2 log(1-s) + (b-1) log(1 + u₋ s/(1-s)) < 0`. -/
theorem lower_core {L K ε δ κ A b u0 lH : ℝ} (hL : 1 ≤ L) (hK : K = L + Real.sqrt L + 1)
    (hε : 0 < ε) (hδ : δ = 16 * K * ε) (hδ2 : δ ≤ 1 / 2) (hb : 1 ≤ b)
    (hu0 : 0 < u0) (hu0ε : u0 ≤ ε) (hu0lo : 1 / (ε * b) ≤ u0) (hκ1 : 1 ≤ κ)
    (hκle : κ ≤ L + Real.sqrt L * Real.sqrt A * Real.sqrt b * ((1 - δ) * u0))
    (hAb : Real.sqrt A ≤ ε * Real.sqrt b) (hlH : lH ≤ 2 * κ * Real.log (1 - δ)) :
    κ / (b * ((1 - δ) * u0) * (1 - (1 - δ) * u0)) < 1 ∧
      lH - κ - 2 * Real.log (1 - κ / (b * ((1 - δ) * u0) * (1 - (1 - δ) * u0))) +
        (b - 1) * Real.log (1 + (1 - δ) * u0 * (κ / (b * ((1 - δ) * u0) * (1 - (1 - δ) * u0))) /
          (1 - κ / (b * ((1 - δ) * u0) * (1 - (1 - δ) * u0)))) < 0 := by
  have hsqL : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL
  have hK3 : 3 ≤ K := by rw [hK]; linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hε96 : ε ≤ 1 / 96 := by
    have : 16 * K * ε ≤ 1 / 2 := hδ ▸ hδ2
    nlinarith
  have hb0 : 0 < b := by linarith
  set um := (1 - δ) * u0 with humdef
  have h1δ : 1 / 2 ≤ 1 - δ := by linarith
  have hum0 : 0 < um := by positivity
  have humu0 : um ≤ u0 := by rw [humdef]; nlinarith
  have humε : um ≤ ε := le_trans humu0 hu0ε
  have hum4 : um ≤ 1 / 4 := by linarith
  have hbum : 1 / (2 * ε) ≤ b * um := by
    have hhalf : u0 / 2 ≤ um := by rw [humdef]; nlinarith
    have h2 : 1 / ε ≤ b * u0 := by
      have := mul_le_mul_of_nonneg_left hu0lo hb0.le
      rwa [show b * (1 / (ε * b)) = 1 / ε by field_simp] at this
    have h3 : b * (u0 / 2) ≤ b * um := mul_le_mul_of_nonneg_left hhalf hb0.le
    have h4 : 1 / (2 * ε) = (1 / ε) / 2 := by ring
    linarith
  have hsb := s_bound (L := L) (κ := κ) (A := A) (b := b) (u := um) (ε := ε) (by linarith) hb0
    hum0 (by linarith) hε hκle hbum hAb
  set s := κ / (b * um * (1 - um)) with hsdef
  have hs0 : 0 ≤ s := by
    have : 0 < 1 - um := by linarith
    positivity
  have hsK : s ≤ 4 * K * ε := by
    have : 2 * (2 * L + Real.sqrt L) ≤ 4 * K := by rw [hK]; linarith
    have hε0 := hε.le
    nlinarith
  have hs8 : s ≤ 1 / 8 := by
    have : 4 * K * ε = δ / 4 := by rw [hδ]; ring
    linarith
  have hs1 : s < 1 := by linarith
  refine ⟨hs1, ?_⟩
  obtain ⟨hlow1, hlow2⟩ := lower_step hκ1 hum0.le humε hs0 hsK hs8 hum4 (by linarith) hε hδ hδ2
  have hchain := log_chain (κ := κ) hum0.le hs0 hs1 hb
  have hbus : b * um * s / (1 - s) = κ / ((1 - um) * (1 - s)) := by
    rw [hsdef]
    have : 1 - um ≠ 0 := by linarith
    have : b * um ≠ 0 := by positivity
    have : 1 - κ / (b * um * (1 - um)) ≠ 0 := by rw [← hsdef]; linarith
    field_simp
  have hkey : κ * (1 / ((1 - um) * (1 - s)) - 1) + 2 * s / (1 - s) =
      -κ + 2 * s / (1 - s) + b * um * s / (1 - s) := by
    rw [hbus]
    have : 1 - um ≠ 0 := by linarith
    have : 1 - s ≠ 0 := by linarith
    field_simp; ring
  linarith

/-- **Theorem `thm:vertex-uniform-root`, bracket (`eq:vertex-uniform-bracket`).**
Let `y_a ∈ [1/(A+1), 1]` solve `H(y_a) = 1`, put `u₀ = √(y_a/b)`,
`ε = √((A+1)/b)`, `K = ℓ + √ℓ + 1`, `δ = 16Kε`, and assume `δ ≤ 1/2`. Let
`S` be any function satisfying the two conclusions of Lemma
`lem:vertex-randomization`:
the Jensen lower bound `(1-u)^A H(bu^2) ≤ S(u)` and the tangent upper bound.
Then `S((1+δ)u₀) > 1` and `S((1-δ)u₀) < 1`. -/
theorem vertex_bracket (m : Fin ℓ → ℕ) (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 1 ≤ b) (S : ℝ → ℝ)
    {ya : ℝ} (hya1 : 1 / ((Atot m : ℝ) + 1) ≤ ya) (hya2 : ya ≤ 1) (hHya : (Hpoly m).eval ya = 1)
    (hJ : ∀ u, 0 < u → u < 1 → (1 - u) ^ Atot m * (Hpoly m).eval (b * u ^ 2) ≤ S u)
    (hT : ∀ u, 0 < u → u < 1 →
      kapH m (b * u ^ 2) / (b * u * (1 - u)) < 1 →
      S u ≤ (1 - u) ^ Atot m * (Hpoly m).eval (b * u ^ 2) * Real.exp (-kapH m (b * u ^ 2)) *
        (1 - kapH m (b * u ^ 2) / (b * u * (1 - u)))⁻¹ ^ 2 *
        (1 + u * (kapH m (b * u ^ 2) / (b * u * (1 - u))) /
          (1 - kapH m (b * u ^ 2) / (b * u * (1 - u)))) ^ (b - 1))
    (hδ : 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) * Real.sqrt (((Atot m : ℝ) + 1) / b) ≤ 1 / 2) :
    1 < S ((1 + 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) * Real.sqrt (((Atot m : ℝ) + 1) / b)) *
        Real.sqrt (ya / b)) ∧
      S ((1 - 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) * Real.sqrt (((Atot m : ℝ) + 1) / b)) *
        Real.sqrt (ya / b)) < 1 := by
  set A : ℝ := (Atot m : ℝ) with hAdef
  set L : ℝ := (ℓ : ℝ)
  set K : ℝ := L + Real.sqrt L + 1 with hK
  set ε : ℝ := Real.sqrt ((A + 1) / b) with hεdef
  set δ : ℝ := 16 * K * ε with hδdef
  set u0 : ℝ := Real.sqrt (ya / b) with hu0def
  have hA : 0 ≤ A := by positivity
  have hb0 : 0 < b := by linarith
  have hL : 1 ≤ L := by simp only [L]; exact_mod_cast hℓ
  have hya0 : 0 < ya := lt_of_lt_of_le (by positivity) hya1
  have hε : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hu0 : 0 < u0 := Real.sqrt_pos.mpr (by positivity)
  have hu0ε : u0 ≤ ε := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hb0.le)
  have hbu0 : b * u0 ^ 2 = ya := by
    rw [hu0def, Real.sq_sqrt (by positivity)]; field_simp
  have hδ0 : 0 ≤ δ := by positivity
  have hεb : ε * Real.sqrt b = Real.sqrt (A + 1) := by
    rw [hεdef, ← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hb0.ne']
  constructor
  · -- upper bracket
    set up := (1 + δ) * u0
    have hκ0pos : 0 < kapH m ya := lt_of_lt_of_le (by positivity) (kapH_ge m hya0)
    have hAu : A * u0 ≤ 2 * kapH m ya * ε := by
      have hk := kapH_ge_half_sqrt m hya0 hya2
      have h1 : A * u0 ≤ Real.sqrt (A * ya) * ε := by
        have e1 : A * u0 = Real.sqrt (A ^ 2 * (ya / b)) := by
          rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA]
        have e2 : Real.sqrt (A * ya) * ε = Real.sqrt (A * ya * ((A + 1) / b)) := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ A * ya)]
        rw [e1, e2]
        apply Real.sqrt_le_sqrt
        rw [show A ^ 2 * (ya / b) = A * ya * (A / b) by ring]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_right (by linarith) hb0.le
      have h2 : Real.sqrt (A * ya) * ε ≤ 2 * kapH m ya * ε :=
        mul_le_mul_of_nonneg_right (by linarith) hε.le
      linarith
    obtain ⟨hup4, hbound, hposb⟩ := upper_step hL hK hε hδdef hδ hκ0pos hA hu0 hu0ε hAu
    have hup0 : 0 < up := by positivity
    have hup1 : up < 1 := by linarith
    have hyp : b * up ^ 2 = (1 + δ) ^ 2 * ya := by rw [← hbu0]; ring
    have hlogH : 2 * kapH m ya * Real.log (1 + δ) ≤ Real.log ((Hpoly m).eval (b * up ^ 2)) := by
      have hinc := logH_increment m hya0 (show ya ≤ b * up ^ 2 by
        rw [hyp]
        exact le_mul_of_one_le_left hya0.le (one_le_pow₀ (by linarith)))
      rw [hHya, Real.log_one, sub_zero] at hinc
      calc 2 * kapH m ya * Real.log (1 + δ)
          = kapH m ya * (Real.log (b * up ^ 2) - Real.log ya) := by
            rw [hyp, Real.log_mul (by positivity) hya0.ne', Real.log_pow]; push_cast; ring
        _ ≤ _ := hinc
    have hlog1 : -(A * (up / (1 - up))) ≤ Real.log ((1 - up) ^ Atot m) := by
      rw [Real.log_pow]
      have h2 := mul_le_mul_of_nonneg_left (log_one_sub_ge hup1) hA
      rw [mul_neg] at h2
      exact h2
    have hHp : 0 < (Hpoly m).eval (b * up ^ 2) := H_eval_pos m (by positivity)
    have hprod : 0 < Real.log ((1 - up) ^ Atot m * (Hpoly m).eval (b * up ^ 2)) := by
      rw [Real.log_mul (by positivity) hHp.ne']
      have : A * up / (1 - up) = A * (up / (1 - up)) := by ring
      linarith
    have h1 : 1 < (1 - up) ^ Atot m * (Hpoly m).eval (b * up ^ 2) := by
      have hpos : 0 < (1 - up) ^ Atot m * (Hpoly m).eval (b * up ^ 2) := by positivity
      rwa [Real.log_pos_iff hpos.le] at hprod
    exact lt_of_lt_of_le h1 (hJ up hup0 hup1)
  · -- lower bracket
    have hε96 : ε ≤ 1 / 96 := by
      have hK3 : 3 ≤ K := by
        have : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL
        rw [hK]; linarith
      have : 16 * K * ε ≤ 1 / 2 := hδ
      have := mul_le_mul_of_nonneg_right hK3 hε.le
      linarith
    set um := (1 - δ) * u0 with humdef
    have hum0 : 0 < um := by
      have : 0 < 1 - δ := by linarith
      positivity
    have hum1 : um < 1 := by
      have : um ≤ u0 := by rw [humdef]; exact mul_le_of_le_one_left hu0.le (by linarith)
      linarith
    set y := b * um ^ 2 with hydef
    have hy0 : 0 < y := by positivity
    have hyya : y = (1 - δ) ^ 2 * ya := by rw [hydef, humdef, ← hbu0]; ring
    set κ := kapH m y with hκdef
    have hκ1 : 1 ≤ κ := le_trans hL (kapH_ge m hy0)
    have hu0lo : 1 / (ε * b) ≤ u0 := by
      have hsq : Real.sqrt (1 / ((A + 1) * b)) = 1 / (ε * b) := by
        rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
        have : ε * ε = (A + 1) / b := Real.mul_self_sqrt (by positivity)
        field_simp
        rw [sq, this]; field_simp
      rw [← hsq, hu0def]
      apply Real.sqrt_le_sqrt
      rw [div_le_div_iff₀ (by positivity) hb0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < A + 1)).mp hya1
      have := mul_le_mul_of_nonneg_right this hb0.le
      linarith
    have hκle : κ ≤ L + Real.sqrt L * Real.sqrt A * Real.sqrt b * um := by
      have := kapH_le m hy0
      have e : Real.sqrt (L * (A * y)) = Real.sqrt L * Real.sqrt A * Real.sqrt b * um := by
        rw [hydef, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity), Real.sqrt_sq hum0.le]
        ring
      rw [e] at this
      exact this
    have hAb : Real.sqrt A ≤ ε * Real.sqrt b := by
      rw [hεb]; exact Real.sqrt_le_sqrt (by linarith)
    have hlogH : Real.log ((Hpoly m).eval y) ≤ 2 * κ * Real.log (1 - δ) := by
      have hinc := logH_increment m hy0 (show y ≤ ya by
        rw [hyya]
        exact mul_le_of_le_one_left hya0.le (pow_le_one₀ (by linarith) (by linarith)))
      rw [hHya, Real.log_one] at hinc
      have e : Real.log ya - Real.log y = -(2 * Real.log (1 - δ)) := by
        rw [hyya, Real.log_mul (pow_pos (by linarith : (0 : ℝ) < 1 - δ) 2).ne' hya0.ne',
          Real.log_pow]; push_cast; ring
      rw [e] at hinc
      linarith
    obtain ⟨hs1, hneg⟩ := lower_core hL hK hε hδdef hδ hb hu0 hu0ε hu0lo hκ1 hκle hAb hlogH
    set s := κ / (b * um * (1 - um)) with hsdef
    have hs0 : 0 ≤ s := by
      have : 0 < 1 - um := by linarith
      positivity
    have hTu := hT um hum0 hum1 hs1
    have hHy : 0 < (Hpoly m).eval y := H_eval_pos m hy0
    have h1s : 0 < 1 - s := by linarith
    have hx : 0 < 1 + um * s / (1 - s) := by positivity
    set R := (Hpoly m).eval y * Real.exp (-κ) * (1 - s)⁻¹ ^ 2 * (1 + um * s / (1 - s)) ^ (b - 1)
      with hRdef
    have hRpos : 0 < R := by positivity
    have hpowA : (1 - um) ^ Atot m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hSle : S um ≤ R := by
      calc S um ≤ (1 - um) ^ Atot m * (Hpoly m).eval y * Real.exp (-κ) * (1 - s)⁻¹ ^ 2 *
            (1 + um * s / (1 - s)) ^ (b - 1) := hTu
        _ = (1 - um) ^ Atot m * R := by rw [hRdef]; ring
        _ ≤ 1 * R := mul_le_mul_of_nonneg_right hpowA hRpos.le
        _ = R := one_mul R
    have hlogR : Real.log R = Real.log ((Hpoly m).eval y) - κ - 2 * Real.log (1 - s) +
        (b - 1) * Real.log (1 + um * s / (1 - s)) := by
      rw [hRdef, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_rpow hx, inv_pow,
        Real.log_inv, Real.log_pow]
      push_cast; ring
    have hR1 : R < 1 := by
      have : Real.log R < 0 := by rw [hlogR]; exact hneg
      rwa [Real.log_neg_iff hRpos] at this
    linarith

end Kagey131.PaperB
