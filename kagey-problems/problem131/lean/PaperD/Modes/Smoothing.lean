import PaperD.Modes.PolyValues
import PaperD.SignChain5

/-!
# Paper D, Theorem `thm:two-modes`, Step 1 (smoothing)

File: `paperD/sec_bulk_applications.tex`. For `N ≥ 3`, `η = 2 N^{-a}` and `z_k = (2k - N) N^{-a}`, the
smoothed second difference is

`V_N(y) = η^{-2} ∑_{k=1}^{N-1} D_N(k) φ(y - z_k)`, `φ(y) = e^{-y²/(2σ²)}/(σ√(2π))`.

Since `φ(y - z_k) = φ(y) e^{-z_k²/(2σ²)} e^{y z_k/σ²}` and the `z_k` are equally spaced, `V_N` is
`ψ(y) ∑ b_k e^{(c + δ k) y}` with `ψ > 0`, `δ = 2N^{-a}/σ² > 0` and `b_k` of the sign of `D_N(k+1)`.
So `lem:descartes` (here `expsum_valuesAtMost`) and `thm:five-blocks` (`five_blocks_signPattern`) give
`smoothedD_valuesAtMost`: `V_N` has values at most `Π₅`.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD
open scoped List

/-- The Gaussian kernel `φ` of width `σ`. -/
noncomputable def gaussKer (σ y : ℝ) : ℝ :=
  Real.exp (-(y ^ 2) / (2 * σ ^ 2)) / (σ * Real.sqrt (2 * Real.pi))

/-- The points `z_k = (2k - N) N^{-a}`. -/
noncomputable def zPt (N : ℕ) (a : ℝ) (k : ℕ) : ℝ := (2 * (k : ℝ) - N) * (N : ℝ) ^ (-a)

/-- The smoothed second difference `V_N` of the elephant bin law. -/
noncomputable def smoothedD (ε a σ : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  ((2 * (N : ℝ) ^ (-a)) ^ 2)⁻¹ *
    ∑ k ∈ Finset.Icc 1 (N - 1), secondDiff (ewBin ε N) k * gaussKer σ (y - zPt N a k)

theorem valuesAtMost_mono {v : ℝ → ℝ} {P Q : List SignType} (h : ValuesAtMost v P)
    (hPQ : P <+ Q) : ValuesAtMost v Q := fun ys hys => (h ys hys).trans hPQ

theorem gaussKer_pos {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : 0 < gaussKer σ y := by
  unfold gaussKer
  positivity

theorem gaussKer_shift {σ : ℝ} (hσ : 0 < σ) (y z : ℝ) :
    gaussKer σ (y - z) = gaussKer σ y * Real.exp (-(z ^ 2) / (2 * σ ^ 2)) *
      Real.exp (y * z / σ ^ 2) := by
  unfold gaussKer
  have : Real.exp (-((y - z) ^ 2) / (2 * σ ^ 2)) = Real.exp (-(y ^ 2) / (2 * σ ^ 2)) *
      Real.exp (-(z ^ 2) / (2 * σ ^ 2)) * Real.exp (y * z / σ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [this]
  ring

/-- `thm:two-modes`, Step 1: the smoothed second difference has values at most `Π₅`. -/
theorem smoothedD_valuesAtMost {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 3 ≤ N)
    (a : ℝ) {σ : ℝ} (hσ : 0 < σ) : ValuesAtMost (smoothedD ε a σ N) piFive := by
  set w : ℕ → ℝ := fun k => Real.exp (-(zPt N a k ^ 2) / (2 * σ ^ 2)) with hw
  set D : ℕ → ℝ := fun k => secondDiff (ewBin ε N) k with hD
  set b : List ℝ := (List.range' 1 (N - 1)).map (fun k => w k * D k) with hb
  have hblen : b.length = N - 1 := by simp [hb]
  have hbget : ∀ i (hi : i < b.length), b[i] = w (i + 1) * D (i + 1) := by
    intro i hi
    simp only [hb, List.getElem_map, List.getElem_range']
    congr 2 <;> ring
  -- the pattern of the coefficients
  have hpat : signPattern b <+ piFive := by
    have e : signPattern b = signPattern ((List.range' 1 (N - 1)).map D) := by
      rw [hb, map_mul_eq_zipWith w D]
      exact signPattern_mul_pos _ _
        (by intro x hx; obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact Real.exp_pos _)
        (by simp)
    rw [e]
    exact five_blocks_signPattern h0 h1 hN
  -- the exponential sum
  set η : ℝ := 2 * (N : ℝ) ^ (-a) with hη
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hηpos : 0 < η := by rw [hη]; positivity
  have hδ : 0 < 2 * (N : ℝ) ^ (-a) / σ ^ 2 := by positivity
  have key := expsum_valuesAtMost b (c := (2 - (N : ℝ)) * (N : ℝ) ^ (-a) / σ ^ 2) hδ
    (ψ := fun y => (η ^ 2)⁻¹ * gaussKer σ y)
    (fun y => by have := gaussKer_pos hσ y; positivity)
  have hfun : smoothedD ε a σ N = fun y => (η ^ 2)⁻¹ * gaussKer σ y *
      ∑ k : Fin b.length, b.get k *
        Real.exp (((2 - (N : ℝ)) * (N : ℝ) ^ (-a) / σ ^ 2 + 2 * (N : ℝ) ^ (-a) / σ ^ 2 * k) * y) := by
    funext y
    unfold smoothedD
    rw [← hη]
    -- reindex the sum over Icc 1 (N-1) as a sum over Fin (N-1)
    have hIcc : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hsum : ∑ k ∈ Finset.Icc 1 (N - 1), secondDiff (ewBin ε N) k * gaussKer σ (y - zPt N a k)
        = ∑ i ∈ Finset.range (N - 1), secondDiff (ewBin ε N) (i + 1) *
            gaussKer σ (y - zPt N a (i + 1)) := by
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1) (fun i _ => ?_)
      rw [add_comm 1 i]
    have hfin : ∑ k : Fin b.length, b.get k *
        Real.exp (((2 - (N : ℝ)) * (N : ℝ) ^ (-a) / σ ^ 2 + 2 * (N : ℝ) ^ (-a) / σ ^ 2 * k) * y)
        = ∑ i ∈ Finset.range (N - 1), w (i + 1) * D (i + 1) *
          Real.exp (((2 - (N : ℝ)) * (N : ℝ) ^ (-a) / σ ^ 2 +
            2 * (N : ℝ) ^ (-a) / σ ^ 2 * i) * y) := by
      rw [← hblen, ← Fin.sum_univ_eq_sum_range
        (fun i => w (i + 1) * D (i + 1) * Real.exp (((2 - (N : ℝ)) * (N : ℝ) ^ (-a) / σ ^ 2 +
            2 * (N : ℝ) ^ (-a) / σ ^ 2 * i) * y)) b.length]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [List.get_eq_getElem]
      rw [hbget i.1 i.2]
    rw [hsum, hfin, mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [gaussKer_shift hσ]
    simp only [hw, hD, zPt]
    have hexp : Real.exp (y * ((2 * ((i + 1 : ℕ) : ℝ) - N) * (N : ℝ) ^ (-a)) / σ ^ 2)
        = Real.exp (((2 - (N : ℝ)) * (N : ℝ) ^ (-a) / σ ^ 2 +
            2 * (N : ℝ) ^ (-a) / σ ^ 2 * i) * y) := by
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [hfun]
  exact valuesAtMost_mono key hpat

end Kagey131.PaperD.Modes
