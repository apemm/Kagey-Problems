import PaperD.U6_Landau

/-!
# Paper D, track U6: the kernel-checked enclosures for Lemma 3.10

The interval `[2^-14, 16]` is cut into 116 pieces (dyadic pieces of relative radius at most
`1/9` below `1`, pieces of width `1/4` above), grouped in four chains `h_i :: t_i` with the
ends `2^-14, 5/512, 3/2, 35/4, 16`. For each needed integrand and each chain the kernel
evaluates `sumIV` (`decide +kernel`); `sumIV_sound` turns the results into an enclosure of the
integral over `[2^-14, 16]`, and `Ioi_of_chunks` adds the two ends `[0, 2^-14]`, `[16, ∞)`.
-/

namespace Kagey131.PaperD.U6

open Real MeasureTheory Set

set_option maxRecDepth 100000
set_option Elab.async false

/-- The model of `sin (π t)` on `|t| ≤ 1/4` (degree 25, 13 terms). -/
def S0 : TM := sinTM0 25 12
/-- The model of `cos (π t)` on `|t| ≤ 1/4` (degree 25, 13 terms). -/
def C0 : TM := cosTM0 25 12

/-- The parameters: degree 12, 13 terms of exp, 13 of log, 80 for `log c`. -/
def mkP (ln : ℤ) (ld k : ℕ) (σ : Bool) : Prm := ⟨12, 12, 12, 80, ln, ld, k, σ, S0, C0⟩

theorem mkP_ok (ln : ℤ) {ld : ℕ} (k : ℕ) (σ : Bool) (h : 0 < ld) : PrmOK (mkP ln ld k σ) :=
  ⟨h, ok_sinTM0 25 12, ok_cosTM0 25 12⟩

/-- The first piece of chain 1. -/
def h1 : Piece := ⟨9, 17, 3⟩
/-- The other pieces of chain 1. -/
def t1 : List Piece := [⟨11, 17, 3⟩, ⟨13, 17, 4⟩, ⟨15, 17, 4⟩, ⟨9, 16, 3⟩, ⟨11, 16, 3⟩, ⟨13, 16, 4⟩, ⟨15, 16, 4⟩, ⟨9, 15, 3⟩, ⟨11, 15, 3⟩, ⟨13, 15, 4⟩, ⟨15, 15, 4⟩, ⟨9, 14, 3⟩, ⟨11, 14, 3⟩, ⟨13, 14, 4⟩, ⟨15, 14, 4⟩, ⟨9, 13, 3⟩, ⟨11, 13, 3⟩, ⟨13, 13, 4⟩, ⟨15, 13, 4⟩, ⟨9, 12, 3⟩, ⟨11, 12, 3⟩, ⟨13, 12, 4⟩, ⟨15, 12, 4⟩, ⟨9, 11, 3⟩, ⟨11, 11, 3⟩, ⟨13, 11, 4⟩, ⟨15, 11, 4⟩, ⟨9, 10, 3⟩]
theorem chain1 : chainOK (h1 :: t1) = true := by decide +kernel
theorem last1 : (h1 :: t1).getLast (List.cons_ne_nil _ _) = ⟨9, 10, 3⟩ := rfl
theorem left1 : leftE h1 = (1 / 16384 : ℝ) := by unfold leftE h1; norm_num
theorem right1 : rightE ⟨9, 10, 3⟩ = (5 / 512 : ℝ) := by unfold rightE; norm_num

/-- The first piece of chain 2. -/
def h2 : Piece := ⟨11, 10, 3⟩
/-- The other pieces of chain 2. -/
def t2 : List Piece := [⟨13, 10, 4⟩, ⟨15, 10, 4⟩, ⟨9, 9, 3⟩, ⟨11, 9, 3⟩, ⟨13, 9, 4⟩, ⟨15, 9, 4⟩, ⟨9, 8, 3⟩, ⟨11, 8, 3⟩, ⟨13, 8, 4⟩, ⟨15, 8, 4⟩, ⟨9, 7, 3⟩, ⟨11, 7, 3⟩, ⟨13, 7, 4⟩, ⟨15, 7, 4⟩, ⟨9, 6, 3⟩, ⟨11, 6, 3⟩, ⟨13, 6, 4⟩, ⟨15, 6, 4⟩, ⟨9, 5, 3⟩, ⟨11, 5, 3⟩, ⟨13, 5, 4⟩, ⟨15, 5, 4⟩, ⟨9, 4, 3⟩, ⟨11, 4, 3⟩, ⟨13, 4, 4⟩, ⟨15, 4, 4⟩, ⟨9, 3, 3⟩, ⟨11, 3, 3⟩]
theorem chain2 : chainOK (h2 :: t2) = true := by decide +kernel
theorem last2 : (h2 :: t2).getLast (List.cons_ne_nil _ _) = ⟨11, 3, 3⟩ := rfl
theorem left2 : leftE h2 = (5 / 512 : ℝ) := by unfold leftE h2; norm_num
theorem right2 : rightE ⟨11, 3, 3⟩ = (3 / 2 : ℝ) := by unfold rightE; norm_num

/-- The first piece of chain 3. -/
def h3 : Piece := ⟨13, 3, 4⟩
/-- The other pieces of chain 3. -/
def t3 : List Piece := [⟨15, 3, 4⟩, ⟨17, 3, 4⟩, ⟨19, 3, 4⟩, ⟨21, 3, 4⟩, ⟨23, 3, 4⟩, ⟨25, 3, 5⟩, ⟨27, 3, 5⟩, ⟨29, 3, 5⟩, ⟨31, 3, 5⟩, ⟨33, 3, 5⟩, ⟨35, 3, 5⟩, ⟨37, 3, 5⟩, ⟨39, 3, 5⟩, ⟨41, 3, 5⟩, ⟨43, 3, 5⟩, ⟨45, 3, 5⟩, ⟨47, 3, 5⟩, ⟨49, 3, 6⟩, ⟨51, 3, 6⟩, ⟨53, 3, 6⟩, ⟨55, 3, 6⟩, ⟨57, 3, 6⟩, ⟨59, 3, 6⟩, ⟨61, 3, 6⟩, ⟨63, 3, 6⟩, ⟨65, 3, 6⟩, ⟨67, 3, 6⟩, ⟨69, 3, 6⟩]
theorem chain3 : chainOK (h3 :: t3) = true := by decide +kernel
theorem last3 : (h3 :: t3).getLast (List.cons_ne_nil _ _) = ⟨69, 3, 6⟩ := rfl
theorem left3 : leftE h3 = (3 / 2 : ℝ) := by unfold leftE h3; norm_num
theorem right3 : rightE ⟨69, 3, 6⟩ = (35 / 4 : ℝ) := by unfold rightE; norm_num

/-- The first piece of chain 4. -/
def h4 : Piece := ⟨71, 3, 6⟩
/-- The other pieces of chain 4. -/
def t4 : List Piece := [⟨73, 3, 6⟩, ⟨75, 3, 6⟩, ⟨77, 3, 6⟩, ⟨79, 3, 6⟩, ⟨81, 3, 6⟩, ⟨83, 3, 6⟩, ⟨85, 3, 6⟩, ⟨87, 3, 6⟩, ⟨89, 3, 6⟩, ⟨91, 3, 6⟩, ⟨93, 3, 6⟩, ⟨95, 3, 6⟩, ⟨97, 3, 7⟩, ⟨99, 3, 7⟩, ⟨101, 3, 7⟩, ⟨103, 3, 7⟩, ⟨105, 3, 7⟩, ⟨107, 3, 7⟩, ⟨109, 3, 7⟩, ⟨111, 3, 7⟩, ⟨113, 3, 7⟩, ⟨115, 3, 7⟩, ⟨117, 3, 7⟩, ⟨119, 3, 7⟩, ⟨121, 3, 7⟩, ⟨123, 3, 7⟩, ⟨125, 3, 7⟩, ⟨127, 3, 7⟩]
theorem chain4 : chainOK (h4 :: t4) = true := by decide +kernel
theorem last4 : (h4 :: t4).getLast (List.cons_ne_nil _ _) = ⟨127, 3, 7⟩ := rfl
theorem left4 : leftE h4 = (35 / 4 : ℝ) := by unfold leftE h4; norm_num
theorem right4 : rightE ⟨127, 3, 7⟩ = (16 : ℝ) := by unfold rightE; norm_num

/-- The enclosure of the integral over a chain. -/
theorem chunk_iv {q : Prm} (hq : PrmOK q) {p pl : Piece} {ps : List Piece} {iv : ℤ × ℤ}
    (hc : chainOK (p :: ps) = true) (h : sumIV q (p :: ps) = some iv)
    (hlast : (p :: ps).getLast (List.cons_ne_nil _ _) = pl) {x0 x1 : ℝ} (hl : leftE p = x0)
    (hr : rightE pl = x1) :
    (iv.1 : ℝ) / D ≤ ∫ s in x0..x1, integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s ∧
      ∫ s in x0..x1, integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s ≤ (iv.2 : ℝ) / D := by
  have := sumIV_sound hq ps p hc h
  rw [hlast, hl, hr] at this
  exact this

/-- The enclosure of `∫_0^∞` from the four chains. -/
theorem Ioi_of_chunks {q : Prm} (hq : PrmOK q) {iv1 iv2 iv3 iv4 : ℤ × ℤ}
    (s1 : sumIV q (h1 :: t1) = some iv1) (s2 : sumIV q (h2 :: t2) = some iv2)
    (s3 : sumIV q (h3 :: t3) = some iv3) (s4 : sumIV q (h4 :: t4) = some iv4)
    (hk : q.k ≤ 3) (hl1 : -1 / 2 ≤ (q.lnum : ℝ) / q.lden) (hl2 : |(q.lnum : ℝ) / q.lden| ≤ 1) :
    ((iv1.1 + iv2.1 + iv3.1 + iv4.1 : ℤ) : ℝ) / D - (3 * ((1 / 2 : ℝ) ^ 14) ^ (q.k + 1) *
        (if q.sin then Real.pi * (1 / 2 : ℝ) ^ 14 else 1) + 16 ^ q.k * Real.exp (-32)) ≤
      ∫ s in Ioi 0, integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s ∧
    ∫ s in Ioi 0, integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s ≤
      ((iv1.2 + iv2.2 + iv3.2 + iv4.2 : ℤ) : ℝ) / D + (3 * ((1 / 2 : ℝ) ^ 14) ^ (q.k + 1) *
        (if q.sin then Real.pi * (1 / 2 : ℝ) ^ 14 else 1) + 16 ^ q.k * Real.exp (-32)) := by
  have c1 := chunk_iv hq chain1 s1 last1 left1 right1
  have c2 := chunk_iv hq chain2 s2 last2 left2 right2
  have c3 := chunk_iv hq chain3 s3 last3 left3 right3
  have c4 := chunk_iv hq chain4 s4 last4 left4 right4
  have hD := D_pos
  set f := integrand q.k ((q.lnum : ℝ) / q.lden) q.sin
  have hf := continuous_integrand q.k ((q.lnum : ℝ) / q.lden) q.sin
  have hmid : ∫ s in (1 / 16384 : ℝ)..16, f s = (∫ s in (1 / 16384 : ℝ)..(5 / 512), f s)
      + (∫ s in (5 / 512 : ℝ)..(3 / 2), f s) + (∫ s in (3 / 2 : ℝ)..(35 / 4), f s)
      + (∫ s in (35 / 4 : ℝ)..16, f s) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _)]
  have hδ0 : (0 : ℝ) < (1 / 2) ^ 14 := by positivity
  have hsplit := integral_Ioi_split hf (integrableOn_integrand _ _ _) hδ0.le
    (by norm_num : (1 / 2 : ℝ) ^ 14 ≤ 16)
  have e14 : ((1 / 2 : ℝ) ^ 14) = 1 / 16384 := by norm_num
  rw [e14] at hsplit
  have hsm := abs_integral_small hδ0 (by norm_num) q.k
    (lam := (q.lnum : ℝ) / q.lden) (by
      calc |(q.lnum : ℝ) / q.lden| * (1 / 2) ^ 14 ≤ 1 * (1 / 2) ^ 14 :=
            mul_le_mul_of_nonneg_right hl2 hδ0.le
        _ ≤ 1 / 16 := by norm_num) q.sin
  rw [e14] at hsm
  have htl := abs_integral_tail hk hl1 q.sin
  rw [abs_le] at hsm htl
  rw [hsplit, hmid]
  push_cast
  simp only [add_div] at c1 c2 c3 c4 ⊢
  rw [e14]
  constructor <;> linarith [c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2, hsm.1, hsm.2, htl.1, htl.2]

/-! ### The kernel computations -/

theorem sA1 : sumIV (mkP (-2229) 10000 1 true) (h1 :: t1) =
    some (80206521342289154060301, 80206521342289599884770) := by decide +kernel
theorem sA2 : sumIV (mkP (-2229) 10000 1 true) (h2 :: t2) =
    some (7224012200108526247484906277, 7224012200150871391594422776) := by decide +kernel
theorem sA3 : sumIV (mkP (-2229) 10000 1 true) (h3 :: t3) =
    some (-7226390220712688034362861293, -7226390220705062428156881099) := by decide +kernel
theorem sA4 : sumIV (mkP (-2229) 10000 1 true) (h4 :: t4) =
    some (-295637385695740529254, -295637385694463027913) := by decide +kernel

theorem sB1 : sumIV (mkP (-2227) 10000 1 true) (h1 :: t1) =
    some (80206403607741294480968, 80206403607741740304679) := by decide +kernel
theorem sB2 : sumIV (mkP (-2227) 10000 1 true) (h2 :: t2) =
    some (7227617868745268647129861229, 7227617868787607859769177906) := by decide +kernel
theorem sB3 : sumIV (mkP (-2227) 10000 1 true) (h3 :: t3) =
    some (-7226068300979776875073875766, -7226068300972154423299505701) := by decide +kernel
theorem sB4 : sumIV (mkP (-2227) 10000 1 true) (h4 :: t4) =
    some (-294882723632394998283, -294882723631119364908) := by decide +kernel

theorem sC1 : sumIV (mkP (-22278299) 100000000 1 true) (h1 :: t1) =
    some (80206452461669568745924, 80206452461670014569949) := by decide +kernel
theorem sC2 : sumIV (mkP (-22278299) 100000000 1 true) (h2 :: t2) =
    some (7226121885679524809570455879, 7226121885721866483559054017) := by decide +kernel
theorem sC3 : sumIV (mkP (-22278299) 100000000 1 true) (h3 :: t3) =
    some (-7226201968683226649682429124, -7226201968675602888894421707) := by decide +kernel
theorem sC4 : sumIV (mkP (-22278299) 100000000 1 true) (h4 :: t4) =
    some (-295195656258241317571, -295195656256964909366) := by decide +kernel

theorem sE1 : sumIV (mkP (-22278297) 100000000 1 true) (h1 :: t1) =
    some (80206452449896115527603, 80206452449896561351626) := by decide +kernel
theorem sE2 : sumIV (mkP (-22278297) 100000000 1 true) (h2 :: t2) =
    some (7226122246233126518965355959, 7226122246275468192360801040) := by decide +kernel
theorem sE3 : sumIV (mkP (-22278297) 100000000 1 true) (h3 :: t3) =
    some (-7226201936485144039393763574, -7226201936477520278921204945) := by decide +kernel
theorem sE4 : sumIV (mkP (-22278297) 100000000 1 true) (h4 :: t4) =
    some (-295195580807081941898, -295195580805805533882) := by decide +kernel

theorem sF1 : sumIV (mkP (-2228) 10000 2 true) (h1 :: t1) =
    some (588672739297833947803, 588672739297838151124) := by decide +kernel
theorem sF2 : sumIV (mkP (-2228) 10000 2 true) (h2 :: t2) =
    some (-18028343081527485509105445131, -18028343081464616969848429411) := by decide +kernel
theorem sF3 : sumIV (mkP (-2228) 10000 2 true) (h3 :: t3) =
    some (-1609598775091765540355700372, -1609598775062579406165176587) := by decide +kernel
theorem sF4 : sumIV (mkP (-2228) 10000 2 true) (h4 :: t4) =
    some (-3773309499011090339395, -3773309498997143185387) := by decide +kernel

theorem sJ1 : sumIV (mkP (-2229) 10000 3 false) (h1 :: t1) =
    some (187400142968761583199, 187400142968762921322) := by decide +kernel
theorem sJ2 : sumIV (mkP (-2229) 10000 3 false) (h2 :: t2) =
    some (104604829162951587843855174580, 104604829163007110466274895574) := by decide +kernel
theorem sJ3 : sumIV (mkP (-2229) 10000 3 false) (h3 :: t3) =
    some (454189768542753162047080343691, 454189768542754163323145894304) := by decide +kernel
theorem sJ4 : sumIV (mkP (-2229) 10000 3 false) (h4 :: t4) =
    some (803399563861458776018738, 803399563861460617737998) := by decide +kernel

theorem sG1 : sumIV (mkP (-2228) 10000 0 true) (h1 :: t1) =
    some (12275292403051915439128146, 12275292403051964510428411) := by decide +kernel
theorem sG2 : sumIV (mkP (-2228) 10000 0 true) (h2 :: t2) =
    some (52283525557505914250939302250, 52283525557540555658768196294) := by decide +kernel
theorem sG3 : sumIV (mkP (-2228) 10000 0 true) (h3 :: t3) =
    some (-7330141929826050036921752011, -7330141929824071561638246434) := by decide +kernel
theorem sG4 : sumIV (mkP (-2228) 10000 0 true) (h4 :: t4) =
    some (-19243368924809407912, -19243368924698998209) := by decide +kernel

end Kagey131.PaperD.U6
