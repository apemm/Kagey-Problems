import PaperD.EJPAnalyticThresholdParam
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Construction of the actual angular inverse chart

Root data for H imply strict decrease and the full positive range of angleF.
An interval order isomorphism constructs the continuous inverse. Its endpoint
limits, Mellin admissibility, the y-coordinate bijection, and the exact second
weight after substitution are consequences. No chart, bijection, endpoint
asymptotic, or weight identity is assumed in `RootData`.
-/

open Set Filter Asymptotics MeasureTheory
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdParam

/-- Order-theoretic inverse construction, with no derivative or inverse assumption. -/
theorem exists_inverse_of_strictAnti {F : ℝ → ℝ} {b : ℝ}
    (hanti : StrictAntiOn F (Ioo 0 b))
    (hpos : ∀ θ ∈ Ioo 0 b, 0 < F θ)
    (hsurj : SurjOn F (Ioo 0 b) (Ioi 0)) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Ioi 0) ∧
      (∀ u ∈ Ioi 0, θ u ∈ Ioo 0 b) ∧ (∀ u ∈ Ioi 0, F (θ u) = u) := by
  let f : (Ioo (0 : ℝ) b)ᵒᵈ → Ioi (0 : ℝ) := fun x => ⟨F (OrderDual.ofDual x).val, hpos (OrderDual.ofDual x).val (OrderDual.ofDual x).property⟩
  have hm : StrictMono f := by
    intro x y hxy
    exact hanti y.property x.property hxy
  have hsu : Function.Surjective f := by
    intro u
    obtain ⟨x,hx,he⟩ := hsurj u.property
    exact ⟨⟨x,hx⟩, Subtype.ext he⟩
  let e : (Ioo (0 : ℝ) b)ᵒᵈ ≃o Ioi (0 : ℝ) := StrictMono.orderIsoOfSurjective f hm hsu
  let θ : ℝ → ℝ := fun u => if hu : u ∈ Ioi (0 : ℝ) then (OrderDual.ofDual (e.symm ⟨u,hu⟩)).val else b
  refine ⟨θ, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hv : Continuous (fun x : (Ioo (0 : ℝ) b)ᵒᵈ => (OrderDual.ofDual x).val) := continuous_subtype_val
    convert hv.comp e.symm.continuous using 1
    ext u
    simp only [Set.domRestrict_apply, θ, dif_pos u.property, Function.comp_def]
  · intro u hu
    simpa only [θ, dif_pos hu] using (OrderDual.ofDual (e.symm ⟨u,hu⟩)).property
  · intro u hu
    have he := congrArg Subtype.val (e.apply_symm_apply ⟨u,hu⟩)
    change F (OrderDual.ofDual (e.symm ⟨u,hu⟩)).val = u at he
    simpa only [θ, dif_pos hu] using he

/-- Endpoint behavior of the inverse follows from order and its actual range. -/
theorem inverse_endpoint_limits {F θ : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hanti : StrictAntiOn F (Ioo 0 b))
    (hpos : ∀ x ∈ Ioo 0 b, 0 < F x)
    (hrange : ∀ u ∈ Ioi 0, θ u ∈ Ioo 0 b)
    (hinv : ∀ u ∈ Ioi 0, F (θ u) = u) :
    Tendsto θ atTop (𝓝 0) ∧ Tendsto θ (𝓝[>] 0) (𝓝 b) := by
  constructor
  · apply tendsto_order.2
    constructor
    · intro r hr
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      exact hr.trans (hrange u hu).1
    · intro r hr
      let δ := min (b/2) (r/2)
      have hd : δ ∈ Ioo 0 b := ⟨lt_min (by linarith) (by linarith),
        (min_le_left _ _).trans_lt (by linarith)⟩
      filter_upwards [eventually_gt_atTop (max 0 (F δ))] with u hu
      have hu0 : 0 < u := (le_max_left _ _).trans_lt hu
      have hf : F δ < u := (le_max_right _ _).trans_lt hu
      have ht : θ u < δ := by
        by_contra hn
        have hle := hanti.antitoneOn hd (hrange u hu0) (le_of_not_gt hn)
        rw [hinv u hu0] at hle
        linarith
      exact ht.trans_le ((min_le_right _ _).trans (by linarith))
  · apply tendsto_order.2
    constructor
    · intro r hr
      let δ := max (b/2) ((r+b)/2)
      have hd : δ ∈ Ioo 0 b := ⟨(by linarith [le_max_left (b/2) ((r+b)/2)]),
        max_lt (by linarith) (by linarith)⟩
      have hp := hpos δ hd
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hp).filter_mono nhdsWithin_le_nhds] with u hu huf
      have ht : δ < θ u := by
        by_contra hn
        have hle := hanti.antitoneOn (hrange u hu) hd (le_of_not_gt hn)
        rw [hinv u hu] at hle
        linarith
      exact (show r ≤ δ by dsimp [δ]; linarith [le_max_right (b/2) ((r+b)/2)]).trans_lt ht
    · intro r hr
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hrange u hu).2.trans hr




/-- Properties supplied by the actual H construction. No parametrization identity
or inverse-chart property is included. The ODE includes the root itself. -/
structure RootData (a : ℝ) (H : ℝ → ℝ) (Y : ℝ) : Prop where
  root_pos : 0 < Y
  root_lt_one : Y < 1
  value_zero : H 0 = 1
  value_root : H Y = 0
  continuous_zero : ContinuousAt H 0
  continuous_root : ContinuousAt H Y
  positive : ∀ y ∈ Ioo 0 Y, 0 < H y
  differentiable : ∀ y ∈ Ioc 0 Y, DifferentiableAt ℝ H y
  ode : ∀ y ∈ Ioc 0 Y, SatisfiesODE a H y

noncomputable def rootAngle (Y : ℝ) := Real.arcsin (Real.sqrt Y)

 theorem rootAngle_mem {Y : ℝ} (hY : 0 < Y) (hY1 : Y < 1) :
    rootAngle Y ∈ Ioo 0 (Real.pi/2) := by
  exact ⟨Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hY),
    Real.arcsin_lt_pi_div_two.mpr (by simpa using Real.sqrt_lt_sqrt hY.le hY1)⟩
 theorem sin_rootAngle {Y : ℝ} (hY : 0 < Y) (hY1 : Y < 1) :
    Real.sin (rootAngle Y) = Real.sqrt Y := by
  exact Real.sin_arcsin (by linarith [Real.sqrt_nonneg Y])
    ((by simpa using Real.sqrt_lt_sqrt hY.le hY1 : Real.sqrt Y < 1).le)

 theorem angle_range {Y θ : ℝ} (hY : 0 < Y) (hY1 : Y < 1)
    (hθ : θ ∈ Ioo 0 (rootAngle Y)) :
    0 < Real.sin θ ∧ 0 < Real.cos θ ∧ Real.sin θ^2 ∈ Ioo 0 Y := by
  have hb := rootAngle_mem hY hY1
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, hb.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo (show θ ∈ Ioo (-(Real.pi/2)) (Real.pi/2) by
    constructor <;> linarith [hθ.1, hθ.2, hb.2, Real.pi_pos])
  have hslt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (show -(Real.pi/2) ≤ θ by linarith [hθ.1, Real.pi_pos]) hb.2.le hθ.2
  rw [sin_rootAngle hY hY1] at hslt
  exact ⟨hs,hc, sq_pos_of_pos hs, by nlinarith [Real.sq_sqrt hY.le]⟩

 theorem angleF_hasDerivAt {a Y θ : ℝ} {H : ℝ → ℝ} (ha : 0 < a)
    (d : RootData a H Y) (hθ : θ ∈ Ioo 0 (rootAngle Y)) :
    HasDerivAt (angleF a H) (-(1/a)*Real.sin θ^(-1-1/a)) θ := by
  obtain ⟨hs,hc,hy⟩ := angle_range d.root_pos d.root_lt_one hθ
  exact hasDerivAt_angleF ha.ne' hs hc
    (d.differentiable _ ⟨hy.1,hy.2.le⟩) (d.ode _ ⟨hy.1,hy.2.le⟩)

 theorem angleF_strictAnti {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a)
    (d : RootData a H Y) : StrictAntiOn (angleF a H) (Ioo 0 (rootAngle Y)) := by
  have hd (θ : ℝ) (hθ : θ ∈ Ioo 0 (rootAngle Y)) := angleF_hasDerivAt ha d hθ
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt)
  intro θ hθ
  rw [interior_Ioo] at hθ
  rw [(hd θ hθ).deriv]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (one_div_pos.mpr ha))
    (Real.rpow_pos_of_pos (angle_range d.root_pos d.root_lt_one hθ).1 _)

 theorem angleF_positive {a Y θ : ℝ} {H : ℝ → ℝ} (d : RootData a H Y)
    (hθ : θ ∈ Ioo 0 (rootAngle Y)) : 0 < angleF a H θ := by
  obtain ⟨hs,hc,hy⟩ := angle_range d.root_pos d.root_lt_one hθ
  exact mul_pos (Real.rpow_pos_of_pos hs _) (d.positive _ hy)

 theorem angleF_endpoint_limits {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a)
    (d : RootData a H Y) :
    Tendsto (angleF a H) (𝓝[>] 0) atTop ∧
    Tendsto (angleF a H) (𝓝[<] (rootAngle Y)) (𝓝 0) := by
  have hb := rootAngle_mem d.root_pos d.root_lt_one
  have hs : Tendsto Real.sin (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨by simpa using (Real.continuous_sin.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds] with θ hθ hp
    exact Real.sin_pos_of_pos_of_lt_pi hθ hp
  have hh : Tendsto (fun θ => H (Real.sin θ^2)) (𝓝[>] 0) (𝓝 1) := by
    have ht : Tendsto (fun θ : ℝ => Real.sin θ^2) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((Real.continuous_sin.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).pow 2
    simpa [Function.comp_def, d.value_zero] using d.continuous_zero.tendsto.comp ht
  constructor
  · exact ((tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos (one_div_pos.mpr ha))).comp hs).atTop_mul_pos
      (by norm_num : (0 : ℝ) < 1) hh
  · have hsroot := sin_rootAngle d.root_pos d.root_lt_one
    have hspos : 0 < Real.sin (rootAngle Y) := by rw [hsroot]; exact Real.sqrt_pos.mpr d.root_pos
    have hc : ContinuousAt (angleF a H) (rootAngle Y) :=
      (Real.continuous_sin.continuousAt.rpow_const (Or.inl hspos.ne')).mul
        (d.continuous_root.comp_of_eq (Real.continuous_sin.continuousAt.pow 2)
          (by rw [hsroot, Real.sq_sqrt d.root_pos.le]))
    have hv : angleF a H (rootAngle Y) = 0 := by
      simp [angleF, hsroot, Real.sq_sqrt d.root_pos.le, d.value_root]
    simpa [hv] using hc.tendsto.mono_left nhdsWithin_le_nhds




 theorem angleF_surjOn {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a)
    (d : RootData a H Y) : SurjOn (angleF a H) (Ioo 0 (rootAngle Y)) (Ioi 0) := by
  have hb := (rootAngle_mem d.root_pos d.root_lt_one).1
  have hc : ContinuousOn (angleF a H) (Ioo 0 (rootAngle Y)) :=
    fun θ hθ => (angleF_hasDerivAt ha d hθ).continuousAt.continuousWithinAt
  obtain ⟨htop,hzero⟩ := angleF_endpoint_limits ha d
  intro u hu
  have hl : ∀ᶠ θ in 𝓝[<] (rootAngle Y), angleF a H θ ≤ u :=
    (hzero.eventually (gt_mem_nhds hu)).mono (fun _ h => h.le)
  have hr : ∀ᶠ θ in 𝓝[>] (0 : ℝ), u ≤ angleF a H θ := htop.eventually_ge_atTop u
  exact isPreconnected_Ioo.intermediate_value₂_eventually₂
    (le_principal_iff.mpr (Ioo_mem_nhdsLT hb)) (le_principal_iff.mpr (Ioo_mem_nhdsGT hb))
    hc continuousOn_const hl hr

 theorem exists_chartOfRoot {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (d : RootData a H Y) :
    ∃ c : AngleChart a H, (∀ u ∈ Ioi 0, c.angle u ∈ Ioo 0 (rootAngle Y)) ∧
      Tendsto c.angle atTop (𝓝 0) ∧ Tendsto c.angle (𝓝[>] 0) (𝓝 (rootAngle Y)) := by
  have hm := angleF_strictAnti ha d
  have hp (θ : ℝ) (hθ : θ ∈ Ioo 0 (rootAngle Y)) := angleF_positive d hθ
  obtain ⟨θ,hc,hr,hi⟩ := exists_inverse_of_strictAnti hm hp (angleF_surjOn ha d)
  let c : AngleChart a H := {
    angle := θ
    continuous := hc
    sin_pos := fun u hu => (angle_range d.root_pos d.root_lt_one (hr u hu)).1
    cos_pos := fun u hu => (angle_range d.root_pos d.root_lt_one (hr u hu)).2.1
    inverse := hi
    differentiable := fun u hu => d.differentiable _
      ⟨(angle_range d.root_pos d.root_lt_one (hr u hu)).2.2.1,
        (angle_range d.root_pos d.root_lt_one (hr u hu)).2.2.2.le⟩
    ode := fun u hu => d.ode _
      ⟨(angle_range d.root_pos d.root_lt_one (hr u hu)).2.2.1,
        (angle_range d.root_pos d.root_lt_one (hr u hu)).2.2.2.le⟩ }
  exact ⟨c,hr,inverse_endpoint_limits (rootAngle_mem d.root_pos d.root_lt_one).1 hm hp hr hi⟩

noncomputable def chartOfRoot {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (d : RootData a H Y) :
    AngleChart a H := (exists_chartOfRoot ha d).choose

 theorem chartOfRoot_range {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (d : RootData a H Y) :
    ∀ u ∈ Ioi 0, (chartOfRoot ha d).angle u ∈ Ioo 0 (rootAngle Y) :=
  (exists_chartOfRoot ha d).choose_spec.1
 theorem chartOfRoot_top {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (d : RootData a H Y) :
    Tendsto (chartOfRoot ha d).angle atTop (𝓝 0) := (exists_chartOfRoot ha d).choose_spec.2.1
 theorem chartOfRoot_zero {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (d : RootData a H Y) :
    Tendsto (chartOfRoot ha d).angle (𝓝[>] 0) (𝓝 (rootAngle Y)) :=
  (exists_chartOfRoot ha d).choose_spec.2.2

 theorem chartOfRoot_twiceAdmissible {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (d : RootData a H Y)
    {z : ℂ} (hz : 0 < z.re) (hz1 : z.re < 1) :
    AnalyticThresholdMellin.TwiceAdmissible
      (fun u => (weight (chartOfRoot ha d) u : ℂ))
      (fun u => (weight₁ (chartOfRoot ha d) u : ℂ))
      (fun u => (weight₂ (chartOfRoot ha d) u : ℂ)) z :=
  twiceAdmissible ha _ d.continuous_zero d.value_zero (chartOfRoot_top ha d) (chartOfRoot_zero ha d) hz hz1

/-- The root is simple, with its derivative and sign forced by the ODE. -/
 theorem root_derivative {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (d : RootData a H Y) :
    deriv H Y = -1/(2*a*Y*Real.sqrt (1-Y)) ∧ deriv H Y < 0 := by
  have hc := Real.sqrt_pos.mpr (sub_pos.mpr d.root_lt_one)
  have hd := d.ode Y ⟨d.root_pos,le_rfl⟩
  unfold SatisfiesODE at hd
  rw [d.value_root] at hd
  have he : deriv H Y = -1/(2*a*Y*Real.sqrt (1-Y)) := by
    field_simp [ha.ne', d.root_pos.ne', hc.ne']
    have hm := congrArg (fun z : ℝ => z*Real.sqrt (1-Y)) hd
    simp only [inv_mul_cancel₀ hc.ne'] at hm
    nlinarith [hm]
  refine ⟨he, ?_⟩
  rw [he]
  exact div_neg_of_neg_of_pos (by norm_num) (by have := d.root_pos; positivity)



noncomputable def yCoordinate (a : ℝ) (H : ℝ → ℝ) (y : ℝ) :=
  H y * y^(-(1/(2*a)))

 theorem yCoordinate_eq_angleF {a Y y : ℝ} {H : ℝ → ℝ} (d : RootData a H Y)
    (hy : y ∈ Ioo 0 Y) : yCoordinate a H y = angleF a H (rootAngle y) := by
  unfold angleF yCoordinate
  rw [sin_rootAngle hy.1 (hy.2.trans d.root_lt_one), Real.sq_sqrt hy.1.le,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hy.1.le]
  rw [show (1/(2 : ℝ)) * -(1/a) = -(1/(2*a)) by ring]
  ring

 theorem rootAngle_lt_rootAngle {Y y : ℝ} (hy : 0 < y) (hyY : y < Y) (hY1 : Y < 1) :
    rootAngle y < rootAngle Y := by
  exact Real.arcsin_lt_arcsin (by linarith [Real.sqrt_nonneg y])
    (Real.sqrt_lt_sqrt hy.le hyY)
    ((by simpa using Real.sqrt_lt_sqrt (hy.le.trans hyY.le) hY1 : Real.sqrt Y < 1).le)

 theorem rootAngle_sin_sq {Y θ : ℝ} (hY : 0 < Y) (hY1 : Y < 1)
    (hθ : θ ∈ Ioo 0 (rootAngle Y)) : rootAngle (Real.sin θ^2) = θ := by
  unfold rootAngle
  rw [Real.sqrt_sq (angle_range hY hY1 hθ).1.le]
  exact Real.arcsin_sin (by linarith [hθ.1, Real.pi_pos])
    (hθ.2.trans (rootAngle_mem hY hY1).2).le

 theorem yCoordinate_bijOn {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (d : RootData a H Y) :
    BijOn (yCoordinate a H) (Ioo 0 Y) (Ioi 0) := by
  have hr (y : ℝ) (hy : y ∈ Ioo 0 Y) : rootAngle y ∈ Ioo 0 (rootAngle Y) :=
    ⟨(rootAngle_mem hy.1 (hy.2.trans d.root_lt_one)).1,
      rootAngle_lt_rootAngle hy.1 hy.2 d.root_lt_one⟩
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [yCoordinate_eq_angleF d hy]
    exact angleF_positive d (hr y hy)
  · intro x hx y hy he
    have hθ := (angleF_strictAnti ha d).injOn (hr x hx) (hr y hy)
      (by simpa [← yCoordinate_eq_angleF d hx, ← yCoordinate_eq_angleF d hy] using he)
    have hs := congrArg (fun θ => Real.sin θ^2) hθ
    simpa [sin_rootAngle hx.1 (hx.2.trans d.root_lt_one),
      sin_rootAngle hy.1 (hy.2.trans d.root_lt_one), Real.sq_sqrt hx.1.le, Real.sq_sqrt hy.1.le] using hs
  · intro u hu
    obtain ⟨θ,hθ,he⟩ := angleF_surjOn ha d hu
    have hy := (angle_range d.root_pos d.root_lt_one hθ).2.2
    refine ⟨Real.sin θ^2, hy, ?_⟩
    rw [yCoordinate_eq_angleF d hy, rootAngle_sin_sq d.root_pos d.root_lt_one hθ, he]

 theorem chartOfRoot_angle_yCoordinate {a Y y : ℝ} {H : ℝ → ℝ} (ha : 0 < a)
    (d : RootData a H Y) (hy : y ∈ Ioo 0 Y) :
    (chartOfRoot ha d).angle (yCoordinate a H y) = rootAngle y := by
  have hu := (yCoordinate_bijOn ha d).mapsTo hy
  apply (angleF_strictAnti ha d).injOn (chartOfRoot_range ha d _ hu)
    ⟨(rootAngle_mem hy.1 (hy.2.trans d.root_lt_one)).1,
      rootAngle_lt_rootAngle hy.1 hy.2 d.root_lt_one⟩
  rw [(chartOfRoot ha d).inverse _ hu, yCoordinate_eq_angleF d hy]

 theorem chartOfRoot_weight₂_yCoordinate {a Y y : ℝ} {H : ℝ → ℝ} (ha : 0 < a)
    (d : RootData a H Y) (hy : y ∈ Ioo 0 Y) :
    weight₂ (chartOfRoot ha d) (yCoordinate a H y) =
      2*a*y^(3/(2*a))*Real.sqrt (1-y)*(1-(1+a)^2*y) := by
  unfold weight₂ angleW₂
  rw [chartOfRoot_angle_yCoordinate ha d hy, sin_rootAngle hy.1 (hy.2.trans d.root_lt_one)]
  have hc : Real.cos (rootAngle y) = Real.sqrt (1-y) := by
    have hcpos := Real.cos_pos_of_mem_Ioo (show rootAngle y ∈ Ioo (-(Real.pi/2)) (Real.pi/2) by
      have hm := rootAngle_mem hy.1 (hy.2.trans d.root_lt_one)
      constructor <;> linarith [hm.1,hm.2,Real.pi_pos])
    have hh : 1-y = Real.cos (rootAngle y)^2 := by
      have := Real.sin_sq_add_cos_sq (rootAngle y)
      rw [sin_rootAngle hy.1 (hy.2.trans d.root_lt_one), Real.sq_sqrt hy.1.le] at this
      linarith
    rw [hh, Real.sqrt_sq hcpos.le]
  rw [hc, Real.sq_sqrt hy.1.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hy.1.le,
    show (1/(2 : ℝ))*(3/a) = 3/(2*a) by ring]

/-- The full model-derived analytic input for Mellin continuation on the larger
strip. In particular, no decay or local-integrability hypothesis is supplied. -/
theorem chartOfRoot_continuedBounds {a Y : ℝ} {H : ℝ → ℝ} (ha : 0 < a)
    (d : RootData a H Y) :
    LocallyIntegrableOn (fun u => (weight₂ (chartOfRoot ha d) u : ℂ)) (Ioi 0) ∧
    (fun u => (weight₂ (chartOfRoot ha d) u : ℂ)) =O[atTop]
      (fun u : ℝ => u ^ (-(3 : ℝ))) ∧
    (fun u => (weight₂ (chartOfRoot ha d) u : ℂ)) =O[𝓝[>] 0]
      (fun u : ℝ => u ^ (-(0 : ℝ))) := by
  let c := chartOfRoot ha d
  refine ⟨?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp_continuousOn
      ((weight₂_continuous ha).comp_continuousOn c.continuous)).locallyIntegrableOn
        measurableSet_Ioi
  · exact ofReal_isBigO (weight_decay c d.continuous_zero d.value_zero
      (chartOfRoot_top ha d)).2.2
  · simpa only [neg_zero, Real.rpow_zero] using ofReal_isBigO
      (weight_zero_bounds ha c (chartOfRoot_zero ha d)).2.2

end Kagey131.PaperD.AnalyticThresholdParam
