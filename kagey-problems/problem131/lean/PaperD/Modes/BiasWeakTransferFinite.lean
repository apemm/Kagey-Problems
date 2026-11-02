import PaperD.Modes.BiasIntervalTransfer
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-! Finite-window averaging preserves the forbidden valley witnesses.
The proof selects maxima in the high blocks and minima in the low blocks;
it makes no variation-diminishing assertion about averaging kernels. -/

namespace Kagey131.PaperD.Modes

open Set Filter
open scoped BigOperators Topology

noncomputable def blockMean (v : ℤ → ℝ) (s : Finset ℤ) : ℝ :=
  (∑ k ∈ s, v k) / s.card

theorem blockMean_mono {v w : ℤ → ℝ} {s : Finset ℤ}
    (h : ∀ k ∈ s, v k ≤ w k) : blockMean v s ≤ blockMean w s := by
  unfold blockMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg s.card)

theorem blockMean_extrema (v : ℤ → ℝ) {s : Finset ℤ} (hs : s.Nonempty) :
    (∃ i ∈ s, v i ≤ blockMean v s) ∧ (∃ j ∈ s, blockMean v s ≤ v j) := by
  classical
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image v hs
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image v hs
  constructor
  · refine ⟨i, hi, (le_div_iff₀ hc).mpr ?_⟩
    calc
      v i * (s.card : ℝ) = ∑ k ∈ s, v i := by simp [mul_comm]
      _ ≤ ∑ k ∈ s, v k := Finset.sum_le_sum hmin
  · refine ⟨j, hj, (div_le_iff₀ hc).mpr ?_⟩
    calc
      (∑ k ∈ s, v k) ≤ ∑ k ∈ s, v j := Finset.sum_le_sum hmax
      _ = v j * (s.card : ℝ) := by simp [mul_comm]

def OrderedBlocks (s t : Finset ℤ) : Prop := ∀ i ∈ s, ∀ j ∈ t, i < j

theorem blockMean_no_two_valleys (v : ℤ → ℝ)
    (hv : ∀ i₀ i₁ i₂ i₃ i₄ : ℤ, i₀ < i₁ → i₁ < i₂ → i₂ < i₃ → i₃ < i₄ →
      v i₁ < v i₀ → v i₁ < v i₂ → v i₃ < v i₂ → v i₃ < v i₄ → False)
    {s₀ s₁ s₂ s₃ s₄ : Finset ℤ}
    (h₀ : s₀.Nonempty) (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (h₃ : s₃.Nonempty) (h₄ : s₄.Nonempty)
    (h01 : OrderedBlocks s₀ s₁) (h12 : OrderedBlocks s₁ s₂)
    (h23 : OrderedBlocks s₂ s₃) (h34 : OrderedBlocks s₃ s₄)
    (h1 : blockMean v s₁ < blockMean v s₀)
    (h2 : blockMean v s₁ < blockMean v s₂)
    (h3 : blockMean v s₃ < blockMean v s₂)
    (h4 : blockMean v s₃ < blockMean v s₄) : False := by
  obtain ⟨i₀, hi₀, hv₀⟩ := (blockMean_extrema v h₀).2
  obtain ⟨i₁, hi₁, hv₁⟩ := (blockMean_extrema v h₁).1
  obtain ⟨i₂, hi₂, hv₂⟩ := (blockMean_extrema v h₂).2
  obtain ⟨i₃, hi₃, hv₃⟩ := (blockMean_extrema v h₃).1
  obtain ⟨i₄, hi₄, hv₄⟩ := (blockMean_extrema v h₄).2
  exact hv i₀ i₁ i₂ i₃ i₄ (h01 _ hi₀ _ hi₁) (h12 _ hi₁ _ hi₂)
    (h23 _ hi₂ _ hi₃) (h34 _ hi₃ _ hi₄)
    (hv₁.trans_lt (h1.trans_le hv₀)) (hv₁.trans_lt (h2.trans_le hv₂))
    (hv₃.trans_lt (h3.trans_le hv₂)) (hv₃.trans_lt (h4.trans_le hv₄))

theorem blockMean_no_valley (v : ℤ → ℝ) (b : ℤ)
    (hv : ∀ i j k : ℤ, b ≤ 2*i+1 → i < j → j < k →
      v j < v i → v j < v k → False)
    {s₀ s₁ s₂ : Finset ℤ}
    (h₀ : s₀.Nonempty) (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (hhalf : ∀ i ∈ s₀, b ≤ 2*i+1)
    (h01 : OrderedBlocks s₀ s₁) (h12 : OrderedBlocks s₁ s₂)
    (h1 : blockMean v s₁ < blockMean v s₀)
    (h2 : blockMean v s₁ < blockMean v s₂) : False := by
  obtain ⟨i₀, hi₀, hv₀⟩ := (blockMean_extrema v h₀).2
  obtain ⟨i₁, hi₁, hv₁⟩ := (blockMean_extrema v h₁).1
  obtain ⟨i₂, hi₂, hv₂⟩ := (blockMean_extrema v h₂).2
  exact hv _ _ _ (hhalf _ hi₀) (h01 _ hi₀ _ hi₁) (h12 _ hi₁ _ hi₂)
    (hv₁.trans_lt (h1.trans_le hv₀)) (hv₁.trans_lt (h2.trans_le hv₂))

end Kagey131.PaperD.Modes
