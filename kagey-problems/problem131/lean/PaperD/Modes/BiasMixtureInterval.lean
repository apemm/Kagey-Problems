import PaperD.Modes.BiasLimitCore
import Mathlib.Topology.Order.Compact

/-!
# The interval of biases with a strict valley

The half-line no-valley bound and reflection dominance are the model-specific
inputs. The rest is an affine mixture argument. No connectedness of the
bimodal set is assumed.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

def StrictValley (g : ℝ → ℝ) : Prop :=
  ∃ x y z, x < y ∧ y < z ∧ g y < g x ∧ g y < g z

noncomputable def reflectedMixture (h : ℝ → ℝ) (q x : ℝ) : ℝ :=
  q*h x+(1-q)*h (-x)

lemma reflectedMixture_reflect (h : ℝ → ℝ) (q x : ℝ) :
    reflectedMixture h (1-q) x = reflectedMixture h q (-x) := by
  simp only [reflectedMixture, neg_neg]
  ring

lemma strictValley_reflect_iff {g : ℝ → ℝ} :
    StrictValley (fun x => g (-x)) ↔ StrictValley g := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,h1,h2⟩
    exact ⟨-z,-y,-x,by linarith,by linarith,h2,h1⟩
  · rintro ⟨x,y,z,hxy,hyz,h1,h2⟩
    refine ⟨-z,-y,-x,by linarith,by linarith,?_,?_⟩
    · simpa only [neg_neg] using h2
    · simpa only [neg_neg] using h1

lemma reflectedMixture_valley_symm (h : ℝ → ℝ) (q : ℝ) :
    StrictValley (reflectedMixture h (1-q)) ↔ StrictValley (reflectedMixture h q) := by
  have he : reflectedMixture h (1-q) = fun x => reflectedMixture h q (-x) :=
    funext (reflectedMixture_reflect h q)
  rw [he]
  exact strictValley_reflect_iff

lemma valley_iff_negative_descent {g : ℝ → ℝ}
    (hdom : ∀ x, 0 ≤ x → g (-x) ≤ g x)
    (hnv : ∀ {x y z : ℝ}, 0 ≤ x → x < y → y < z →
      g y < g x → g y < g z → False) :
    StrictValley g ↔ ∃ x y, x < y ∧ y ≤ 0 ∧ g y < g x := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,h1,h2⟩
    have hx : x < 0 := lt_of_not_ge (fun h => hnv h hxy hyz h1 h2)
    by_cases hy : y ≤ 0
    · exact ⟨x,y,hxy,hy,h1⟩
    · have h0y : 0 < y := lt_of_not_ge hy
      have hh : g 0 ≤ g y := le_of_not_gt (fun h => hnv le_rfl h0y hyz h h2)
      exact ⟨x,0,hx,le_rfl,hh.trans_lt h1⟩
  · rintro ⟨x,y,hxy,hy,hdec⟩
    have hx : x < 0 := hxy.trans_le hy
    have hh := hdom (-x) (by linarith)
    simp only [neg_neg] at hh
    exact ⟨x,y,-x,hxy,by linarith,hdec,hdec.trans_le hh⟩

lemma monotone_negative_of_no_valley {h : ℝ → ℝ}
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) (hnv : ¬StrictValley h) :
    MonotoneOn h (Iic 0) := by
  intro x hx y hy hxy
  change x ≤ 0 at hx
  change y ≤ 0 at hy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  · apply le_of_not_gt
    intro hdec
    have hxn : x < 0 := hxy.trans_le hy
    have hh := hdom (-x) (by linarith)
    simp only [neg_neg] at hh
    exact hnv ⟨x,y,-x,hxy,by linarith,hdec,hdec.trans_le hh⟩

lemma reflectedMixture_dominance {h : ℝ → ℝ}
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) {q : ℝ} (hq : 1/2 ≤ q)
    {x : ℝ} (hx : 0 ≤ x) : reflectedMixture h q (-x) ≤ reflectedMixture h q x := by
  have hh := hdom x hx
  dsimp [reflectedMixture]
  simp only [neg_neg]
  nlinarith

lemma affine_descent_persists {A B q r : ℝ}
    (hA : A ≤ 0) (hq : q ≤ 1) (hrq : r ≤ q)
    (hpos : 0 < q*A+(1-q)*B) : 0 < r*A+(1-r)*B := by
  have hAB : A < B := by
    by_contra hn
    have hBA : B ≤ A := le_of_not_gt hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hBA)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hrq) (sub_nonneg.mpr hAB.le)]

theorem reflectedMixture_valley_downward {h : ℝ → ℝ}
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) (hnv : ¬StrictValley h)
    (hright : ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ {x y z : ℝ},
      0 ≤ x → x < y → y < z →
      reflectedMixture h q y < reflectedMixture h q x →
      reflectedMixture h q y < reflectedMixture h q z → False)
    {q r : ℝ} (hr : 1/2 ≤ r) (hrq : r ≤ q) (hq : q ≤ 1)
    (hv : StrictValley (reflectedMixture h q)) :
    StrictValley (reflectedMixture h r) := by
  have hq0 : 1/2 ≤ q := hr.trans hrq
  obtain ⟨x,y,hxy,hy,hdec⟩ :=
    (valley_iff_negative_descent
      (fun x hx => reflectedMixture_dominance hdom hq0 hx)
      (hright q ⟨hq0,hq⟩)).mp hv
  have hh := monotone_negative_of_no_valley hdom hnv
    (show x ∈ Iic 0 from hxy.le.trans hy) hy hxy.le
  have hp := affine_descent_persists (A := h x-h y) (B := h (-x)-h (-y))
    (by linarith) hq hrq (by dsimp [reflectedMixture] at hdec; nlinarith)
  apply (valley_iff_negative_descent
    (fun x hx => reflectedMixture_dominance hdom hr hx)
    (hright r ⟨hr,hrq.trans hq⟩)).mpr
  exact ⟨x,y,hxy,hy,by dsimp [reflectedMixture]; nlinarith⟩

lemma reflectedMixture_valley_eventually {h : ℝ → ℝ} {q : ℝ}
    (hv : StrictValley (reflectedMixture h q)) :
    ∀ᶠ r in 𝓝 q, StrictValley (reflectedMixture h r) := by
  obtain ⟨x,y,z,hxy,hyz,h1,h2⟩ := hv
  have hc : ∀ u, Continuous (fun r => reflectedMixture h r u) := by
    intro u
    unfold reflectedMixture
    fun_prop
  have he1 := (hc y).continuousAt.eventually_lt (hc x).continuousAt h1
  have he2 := (hc y).continuousAt.eventually_lt (hc z).continuousAt h2
  filter_upwards [he1,he2] with r hr1 hr2
  exact ⟨x,y,z,hxy,hyz,hr1,hr2⟩

/-- The strict-valley biases form one open interval centred at one half.
The interval is empty when its lower endpoint is one half. -/
theorem reflectedMixture_valley_interval {h : ℝ → ℝ}
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) (hnv : ¬StrictValley h)
    (hright : ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ {x y z : ℝ},
      0 ≤ x → x < y → y < z →
      reflectedMixture h q y < reflectedMixture h q x →
      reflectedMixture h q y < reflectedMixture h q z → False) :
    ∃ b ∈ Icc (0 : ℝ) (1/2), ∀ q ∈ Icc (0 : ℝ) 1,
      StrictValley (reflectedMixture h q) ↔ b < q ∧ q < 1-b := by
  classical
  by_cases hf : StrictValley (reflectedMixture h (1/2))
  · let S : Set ℝ := {q | 1/2 ≤ q ∧ q ≤ 1 ∧ StrictValley (reflectedMixture h q)}
    have hS : S.Nonempty := ⟨1/2,le_rfl,by norm_num,hf⟩
    have hSb : BddAbove S := ⟨1,fun _ h => h.2.1⟩
    let c := sSup S
    have hc0 : 1/2 ≤ c := le_csSup hSb ⟨le_rfl,by norm_num,hf⟩
    have hc1 : c ≤ 1 := csSup_le hS (fun _ h => h.2.1)
    have hbelow : ∀ q ∈ Icc (1/2 : ℝ) 1,
        StrictValley (reflectedMixture h q) ↔ q < c := by
      intro q hq
      constructor
      · intro hv
        have hq1 : q < 1 := lt_of_le_of_ne hq.2 (by
          intro he
          subst q
          apply hnv
          have he : reflectedMixture h 1 = h := by
            funext x
            simp [reflectedMixture]
          rwa [he] at hv)
        obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp
          (reflectedMixture_valley_eventually hv)
        let d := min δ (1-q)/2
        have hd : 0 < d := by dsimp [d]; positivity
        have hdδ : d < δ := by dsimp [d]; have := min_le_left δ (1-q); linarith
        have hdq : d < 1-q := by dsimp [d]; have := min_le_right δ (1-q); linarith
        have hpv : StrictValley (reflectedMixture h (q+d)) :=
          hh (by simpa [Real.dist_eq,abs_of_pos hd] using hdδ)
        have hp : q+d ∈ S := ⟨by linarith [hq.1],by linarith,hpv⟩
        exact lt_csSup_of_lt hSb hp (by linarith)
      · intro hqc
        obtain ⟨p,hp,hqp⟩ := exists_lt_of_lt_csSup hS hqc
        exact reflectedMixture_valley_downward hdom hnv hright hq.1 hqp.le hp.2.1 hp.2.2
    refine ⟨1-c,⟨by linarith,by linarith⟩,?_⟩
    intro q hq
    by_cases hqhalf : 1/2 ≤ q
    · have hh := hbelow q ⟨hqhalf,hq.2⟩
      have hcstrict : 1/2 < c := (hbelow (1/2) ⟨le_rfl,by norm_num⟩).mp hf
      constructor
      · intro hv
        have := hh.mp hv
        constructor <;> linarith
      · intro hv
        exact hh.mpr (by linarith [hv.2])
    · have hqhalf' : q < 1/2 := lt_of_not_ge hqhalf
      have hh := hbelow (1-q) ⟨by linarith,by linarith [hq.1]⟩
      constructor
      · intro hv
        have hvc := hh.mp ((reflectedMixture_valley_symm h q).mpr hv)
        constructor <;> linarith
      · intro hv
        exact (reflectedMixture_valley_symm h q).mp (hh.mpr (by linarith [hv.1]))
  · refine ⟨1/2,⟨by norm_num,le_rfl⟩,?_⟩
    intro q hq
    constructor
    · intro hv
      exfalso
      apply hf
      by_cases hhalf : 1/2 ≤ q
      · exact reflectedMixture_valley_downward hdom hnv hright le_rfl hhalf hq.2 hv
      · exact reflectedMixture_valley_downward hdom hnv hright le_rfl
          (by linarith) (by linarith [hq.1]) ((reflectedMixture_valley_symm h q).mpr hv)
    · intro hh
      linarith [hh.1,hh.2]

end Kagey131.PaperD.Modes
