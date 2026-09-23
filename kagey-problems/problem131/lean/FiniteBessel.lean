import Std
/-!
Finite algebraic foundations for the uniform Bessel bounds in Problem 131.
This Lean verification code was developed with OpenAI Codex assistance.
The analytic infinite-series identities and probability model are not formalized here.
All scalar parameters in this file are rational. Lean 4.33.1, Std only.
-/
namespace Kagey131

def clip (t : Rat) : Rat := if t ≤ 1 then 1-t else 0

theorem clip_bounds (t : Rat) (ht : 0≤t) :
    0≤clip t ∧ clip t≤1 ∧ 1-clip t≤t := by
  unfold clip
  split <;> grind

theorem unit_product_bounds (a b : Rat) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1) :
    0≤a*b ∧ a*b≤1 := by
  have h0 := Rat.mul_nonneg ha.1 hb.1
  have h1 := Rat.mul_le_mul_of_nonneg_right ha.2 hb.1
  grind

theorem product_deficit (a b A B : Rat)
    (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1)
    (hA : 1-a≤A) (hB : 1-b≤B) :
    0≤1-a*b ∧ 1-a*b≤A+B := by
  have hp := unit_product_bounds a b ha hb
  have hm := Rat.mul_nonneg (show 0≤1-a by grind) (show 0≤1-b by grind)
  grind

def clipProduct : List Rat → Rat
  | [] => 1
  | t::ts => clip t * clipProduct ts

def total : List Rat → Rat
  | [] => 0
  | t::ts => t + total ts

/-- The union-bound inequality for an arbitrary finite family of clipped factors.
It remains valid when some factor parameter exceeds one. -/
theorem finite_product_deficit (ts : List Rat) (ht : ∀t∈ts, 0≤t) :
    0≤clipProduct ts ∧ clipProduct ts≤1 ∧
    0≤1-clipProduct ts ∧ 1-clipProduct ts≤total ts := by
  induction ts with
  | nil => simp [clipProduct, total]; grind
  | cons t ts ih =>
    have hfirst : 0≤t := ht t (by simp)
    have hrest : ∀s∈ts, 0≤s := by intro s hs; exact ht s (by simp [hs])
    have hs := ih hrest
    have hc := clip_bounds t hfirst
    have hp := unit_product_bounds (clip t) (clipProduct ts) ⟨hc.1,hc.2.1⟩ ⟨hs.1,hs.2.1⟩
    have hd := product_deficit (clip t) (clipProduct ts) t (total ts)
      ⟨hc.1,hc.2.1⟩ ⟨hs.1,hs.2.1⟩ hc.2.2 hs.2.2.2
    simpa [clipProduct,total] using And.intro hp.1 (And.intro hp.2 hd)

def fallingProduct (v : Rat) : Nat → Rat
  | 0 => 1
  | r+1 => fallingProduct v r * clip ((r+1:Nat)*v)

/-- The deficit of the normalized falling factorial, including its zero tail. -/
theorem falling_product_deficit (v : Rat) (hv : 0≤v) (r : Nat) :
    0≤fallingProduct v r ∧ fallingProduct v r≤1 ∧
    0≤1-fallingProduct v r ∧
    1-fallingProduct v r≤v*(r:Rat)*((r:Rat)+1)/2 := by
  induction r with
  | zero => simp [fallingProduct]; grind
  | succ r ih =>
    have hr : 0≤(r:Rat) := Rat.natCast_nonneg
    have hc := clip_bounds (((r+1:Nat):Rat)*v)
      (Rat.mul_nonneg Rat.natCast_nonneg hv)
    have hp := unit_product_bounds (fallingProduct v r) (clip (((r+1:Nat):Rat)*v))
      ⟨ih.1,ih.2.1⟩ ⟨hc.1,hc.2.1⟩
    have hd := product_deficit (fallingProduct v r) (clip (((r+1:Nat):Rat)*v))
      (v*(r:Rat)*((r:Rat)+1)/2) (((r+1:Nat):Rat)*v)
      ⟨ih.1,ih.2.1⟩ ⟨hc.1,hc.2.1⟩ ih.2.2.2 hc.2.2
    have he : v*(r:Rat)*((r:Rat)+1)/2 + (((r+1:Nat):Rat)*v) =
        v*((r+1:Nat):Rat)*(((r+1:Nat):Rat)+1)/2 := by
      rw [Rat.natCast_add]
      grind
    simpa [fallingProduct,he] using And.intro hp.1 (And.intro hp.2 (And.intro hd.1 (show
      1-fallingProduct v r * clip (((r+1:Nat):Rat)*v) ≤
      v*((r+1:Nat):Rat)*(((r+1:Nat):Rat)+1)/2 by grind)))

/-- The coefficient defect used in the periodic Bessel bound, for two arbitrary bin sizes.
Set v=1/a, w=1/b to obtain r(r+1)(1/a+1/b)/2. -/
theorem paired_falling_deficit (v w : Rat) (hv : 0≤v) (hw : 0≤w) (r : Nat) :
    0≤1-fallingProduct v r * fallingProduct w r ∧
    1-fallingProduct v r * fallingProduct w r ≤
      (v+w)*(r:Rat)*((r:Rat)+1)/2 := by
  have ha := falling_product_deficit v hv r
  have hb := falling_product_deficit w hw r
  have hd := product_deficit (fallingProduct v r) (fallingProduct w r)
    (v*(r:Rat)*((r:Rat)+1)/2) (w*(r:Rat)*((r:Rat)+1)/2)
    ⟨ha.1,ha.2.1⟩ ⟨hb.1,hb.2.1⟩ ha.2.2.2 hb.2.2.2
  grind

#print axioms finite_product_deficit
#print axioms falling_product_deficit
#print axioms paired_falling_deficit




/-- Convex averaging preserves interval bounds and combines the deficit estimates. -/
theorem convex_deficit (a b A B α β : Rat)
    (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1)
    (hA : 1-a≤A) (hB : 1-b≤B)
    (hα : 0≤α) (hβ : 0≤β) (hs : α+β=1) :
    0≤α*a+β*b ∧ α*a+β*b≤1 ∧
    0≤1-(α*a+β*b) ∧ 1-(α*a+β*b)≤α*A+β*B := by
  have h0 := Rat.mul_nonneg hα ha.1
  have h1 := Rat.mul_nonneg hβ hb.1
  have h2 := Rat.mul_le_mul_of_nonneg_left ha.2 hα
  have h3 := Rat.mul_le_mul_of_nonneg_left hb.2 hβ
  have h4 := Rat.mul_le_mul_of_nonneg_left hA hα
  have h5 := Rat.mul_le_mul_of_nonneg_left hB hβ
  grind

/-- The weighted, shifted coefficient defect for the free-boundary Bessel approximation.
In the application v=1/a, w=1/b, α=a/(a+b), β=b/(a+b). -/
theorem shifted_paired_falling_deficit (v w α β : Rat)
    (hv : 0≤v) (hw : 0≤w) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β=1) (r : Nat) :
    let E := α*fallingProduct v (r+1)*fallingProduct w r +
      β*fallingProduct v r*fallingProduct w (r+1)
    0≤E ∧ E≤1 ∧ 0≤1-E ∧
      1-E≤(v+w)*(r:Rat)*((r:Rat)+1)/2 + ((r:Rat)+1)*(α*v+β*w) := by
  have ha := falling_product_deficit v hv r
  have hb := falling_product_deficit w hw r
  have hA := falling_product_deficit v hv (r+1)
  have hB := falling_product_deficit w hw (r+1)
  have hi := unit_product_bounds (fallingProduct v (r+1)) (fallingProduct w r)
    ⟨hA.1,hA.2.1⟩ ⟨hb.1,hb.2.1⟩
  have hj := unit_product_bounds (fallingProduct v r) (fallingProduct w (r+1))
    ⟨ha.1,ha.2.1⟩ ⟨hB.1,hB.2.1⟩
  have hdi := product_deficit (fallingProduct v (r+1)) (fallingProduct w r)
    (v*((r+1:Nat):Rat)*(((r+1:Nat):Rat)+1)/2)
    (w*(r:Rat)*((r:Rat)+1)/2) ⟨hA.1,hA.2.1⟩ ⟨hb.1,hb.2.1⟩ hA.2.2.2 hb.2.2.2
  have hdj := product_deficit (fallingProduct v r) (fallingProduct w (r+1))
    (v*(r:Rat)*((r:Rat)+1)/2)
    (w*((r+1:Nat):Rat)*(((r+1:Nat):Rat)+1)/2) ⟨ha.1,ha.2.1⟩ ⟨hB.1,hB.2.1⟩ ha.2.2.2 hB.2.2.2
  have hc := convex_deficit (fallingProduct v (r+1)*fallingProduct w r)
    (fallingProduct v r*fallingProduct w (r+1))
    (v*((r+1:Nat):Rat)*(((r+1:Nat):Rat)+1)/2 + w*(r:Rat)*((r:Rat)+1)/2)
    (v*(r:Rat)*((r:Rat)+1)/2 + w*((r+1:Nat):Rat)*(((r+1:Nat):Rat)+1)/2)
    α β hi hj hdi.2 hdj.2 hα hβ hs
  simp only [Rat.natCast_add] at hc
  have he :
      α*(v*((r:Rat)+1)*((r:Rat)+1+1)/2 + w*(r:Rat)*((r:Rat)+1)/2) +
      β*(v*(r:Rat)*((r:Rat)+1)/2 + w*((r:Rat)+1)*((r:Rat)+1+1)/2) =
      (v+w)*(r:Rat)*((r:Rat)+1)/2 + ((r:Rat)+1)*(α*v+β*w) := by
    grind
  dsimp
  grind

structure WeightedTerm where
  weight : Rat
  value : Rat
  bound : Rat

def unmaskedSum : List WeightedTerm → Rat
  | [] => 0
  | t::ts => t.weight + unmaskedSum ts

def maskedSum : List WeightedTerm → Rat
  | [] => 0
  | t::ts => t.weight*t.value + maskedSum ts

def errorSum : List WeightedTerm → Rat
  | [] => 0
  | t::ts => t.weight*t.bound + errorSum ts

/-- Arbitrary finite nonnegative weighted sums preserve the coefficient deficit bound.
Passing to an infinite Bessel series requires an additional analytic argument. -/
theorem weighted_sum_deficit (ts : List WeightedTerm)
    (ht : ∀t∈ts, 0≤t.weight ∧ 0≤t.value ∧ t.value≤1 ∧ 1-t.value≤t.bound) :
    0≤unmaskedSum ts-maskedSum ts ∧
    unmaskedSum ts-maskedSum ts≤errorSum ts := by
  induction ts with
  | nil => simp [unmaskedSum,maskedSum,errorSum]; grind
  | cons t ts ih =>
    have ht0 := ht t (by simp)
    have hrest : ∀s∈ts, 0≤s.weight ∧ 0≤s.value ∧ s.value≤1 ∧ 1-s.value≤s.bound := by
      intro s hs; exact ht s (by simp [hs])
    have hi := ih hrest
    have hlo := Rat.mul_nonneg ht0.1 (show 0≤1-t.value by grind)
    have hhi := Rat.mul_le_mul_of_nonneg_left ht0.2.2.2 ht0.1
    dsimp [unmaskedSum,maskedSum,errorSum]
    grind

#print axioms convex_deficit
#print axioms shifted_paired_falling_deficit
#print axioms weighted_sum_deficit


#print axioms clip_bounds
#print axioms unit_product_bounds
#print axioms product_deficit
end Kagey131
