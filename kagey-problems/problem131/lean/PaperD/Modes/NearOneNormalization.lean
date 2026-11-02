import PaperD.Modes.NearOneMixture
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Kagey131.PaperD.Modes

open Set Filter Topology MeasureTheory

lemma affineDensityProfile_integrable {p : ℝ → ℝ} {A s : ℝ}
    (hs : 0 < s) (hp : Integrable p) : Integrable (affineDensityProfile p A s) := by
  exact ((hp.comp_sub_left A).comp_mul_left' hs.ne').const_mul s

lemma affineDensityProfile_integral {p : ℝ → ℝ} {A s : ℝ} (hs : 0 < s) :
    (∫ z, affineDensityProfile p A s z) = ∫ x, p x := by
  simp only [affineDensityProfile,integral_const_mul]
  rw [Measure.integral_comp_mul_left (fun x => p (A-x)) s]
  rw [integral_sub_left_eq_self p volume A]
  simp [smul_eq_mul,abs_of_pos (inv_pos.mpr hs),hs.ne']

/-- The moving fold boundary recedes under precisely the near-one scaling. -/
theorem near_one_cutoff_tendsto {ε : ℕ → ℝ} (hpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => (1+2*ε n*Real.log (1/ε n))/(2*ε n)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have he : 0 < 1/(2*(|b|+1)) := by positivity
  have hev := hε.eventually (Iio_mem_nhds (lt_min (by norm_num : (0:ℝ)<1) he))
  filter_upwards [hev] with n hn
  have hn1 : ε n < 1 := lt_of_lt_of_le hn (min_le_left _ _)
  have hnb : ε n < 1/(2*(|b|+1)) := lt_of_lt_of_le hn (min_le_right _ _)
  have hm : ε n*(2*(|b|+1)) < 1 := (lt_div_iff₀ (by positivity)).mp hnb
  have hinv : |b|+1 < 1/(2*ε n) :=
    (lt_div_iff₀ (mul_pos (by norm_num) (hpos n))).mpr (by nlinarith)
  have hlog : 0 ≤ Real.log (1/ε n) := Real.log_nonneg ((le_div_iff₀ (hpos n)).mpr (by linarith))
  have hid : (1+2*ε n*Real.log (1/ε n))/(2*ε n) = 1/(2*ε n)+Real.log (1/ε n) := by
    field_simp [(hpos n).ne']
  rw [hid]
  linarith [le_abs_self b]

end Kagey131.PaperD.Modes
