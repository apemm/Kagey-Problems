import Std
/-!
Exact finite coefficient and crossing algebra for Problem 131.
This Lean verification code was generated with Claude Opus 5.5.
This file formalizes falling-product coefficients rather than assuming a
library theorem connecting them to binary words or binomial coefficients.
-/
namespace Kagey131

/-- The unnormalized product (r!)^2 C(a-1,r) C(b-1,r).
Natural subtraction gives the correct zero tail automatically. -/
def pairProduct (a b : Nat) : Nat → Nat
  | 0 => 1
  | r+1 => pairProduct a b r * ((a-1-r)*(b-1-r))

theorem inward_factor_identity (a b j : Int) :
    (a-j)*(b-2-j)-(a-1-j)*(b-1-j)=b-a-1 := by grind

theorem inward_factor_monotone (a b j : Nat) (hab : a+1≤b) :
    (a-1-j)*(b-1-j) ≤ (a-j)*(b-2-j) := by
  by_cases hj : j<a-1
  · have ha : a-j=(a-1-j)+1 := by omega
    have hb : b-1-j=(b-2-j)+1 := by omega
    have hc : b-2-j=(a-1-j)+(b-a-1) := by omega
    rw [ha,hb,hc]
    grind
  · have hz : a-1-j=0 := by omega
    simp [hz]

/-- Every falling-product coefficient increases weakly toward the center,
including indices past the support. -/
theorem inward_product_monotone (a b r : Nat) (hab : a+1≤b) :
    pairProduct a b r ≤ pairProduct (a+1) (b-1) r := by
  induction r with
  | zero => simp [pairProduct]
  | succ r ih =>
    have hf := inward_factor_monotone a b r hab
    have ha : a+1-1-r=a-r := by omega
    have hb : b-1-1-r=b-2-r := by omega
    simpa [pairProduct,ha,hb] using Nat.mul_le_mul ih hf

/-- The cubic run coefficient is strictly larger before reaching the center. -/
theorem inward_first_product_strict (a b : Nat) (ha : 1≤a) (hab : a+1<b) :
    pairProduct a b 1 < pairProduct (a+1) (b-1) 1 := by
  have hx : a=(a-1)+1 := by omega
  have hy : b-1=(b-2)+1 := by omega
  have hz : b-2=(a-1)+(b-a-1) := by omega
  have hd : 0<b-a-1 := by omega
  simp only [pairProduct]
  have hb : b-1-1=b-2 := by omega
  simp only [Nat.sub_zero, Nat.one_mul, Nat.add_sub_cancel, hb]
  rw [hx,hy,hz]
  grind

/-- At fixed left bin label, all falling-product coefficients increase with size. -/
theorem longer_product_monotone (a b r : Nat) :
    pairProduct a b r ≤ pairProduct a (b+1) r := by
  induction r with
  | zero => simp [pairProduct]
  | succ r ih =>
    have hf : (a-1-r)*(b-1-r)≤(a-1-r)*(b+1-1-r) := by
      exact Nat.mul_le_mul (by omega) (by omega)
    exact Nat.mul_le_mul ih hf

/-- Clearing denominators in the even-run coefficient simplification.
The hypotheses are precisely the two binomial coefficient recurrences. -/
theorem even_run_coefficient_identity (a b r A B A₁ B₁ : Rat)
    (ha : (r+1)*A₁=(a-1-r)*A) (hb : (r+1)*B₁=(b-1-r)*B) :
    (r+1)*(A₁*B+A*B₁)=(a+b-2-2*r)*A*B := by grind

/-- Adjacent-bin equality for free boundaries is a quadratic in switching odds. -/
def adjacentFree (N u : Rat) : Rat := 2*u+(N-2)*u*u

def adjacentPeriodic (N u : Rat) : Rat := N*u*u

/-- A square-root parameter gives the exact free adjacent crossing without
introducing any analytic square-root axioms. -/
theorem free_adjacent_crossing (N s u : Rat)
    (hs : s*s=N-1) (hu : (1+s)*u=1) : adjacentFree N u=1 := by
  unfold adjacentFree
  grind

theorem free_adjacent_root_unique (N u v : Rat) (hN : 2≤N)
    (hu : 0≤u) (hv : 0≤v)
    (hru : adjacentFree N u=1) (hrv : adjacentFree N v=1) : u=v := by
  have hfactor : (u-v)*(2+(N-2)*(u+v))=0 := by
    unfold adjacentFree at hru hrv
    grind
  have hn := Rat.mul_nonneg (show 0≤N-2 by grind) (show 0≤u+v by grind)
  have hpos : 0<2+(N-2)*(u+v) := by grind
  rcases Rat.mul_eq_zero.mp hfactor with h0|h0 <;> grind

/-- For periodic boundaries the exact adjacent crossing is N*u^2=1. -/
theorem periodic_adjacent_crossing (N s u : Rat)
    (hs : s*s=N) (hu : s*u=1) : adjacentPeriodic N u=1 := by
  unfold adjacentPeriodic
  grind

theorem periodic_adjacent_root_unique (N u v : Rat) (hN : 0<N)
    (hu : 0<u) (hv : 0<v)
    (hru : adjacentPeriodic N u=1) (hrv : adjacentPeriodic N v=1) : u=v := by
  have he : N*(u-v)*(u+v)=0 := by
    unfold adjacentPeriodic at hru hrv
    grind
  have hsum : 0<u+v := by grind
  have hN0 : N≠0 := by grind
  have hs0 : u+v≠0 := by grind
  rcases Rat.mul_eq_zero.mp he with hp|hp
  · rcases Rat.mul_eq_zero.mp hp with hn|hd <;> grind
  · grind

/-- The two Bessel-series error contributions simplify to a bin-independent
relative error once H/2=c/s and 2c/N=1/s. Here q denotes 1/s. -/
theorem free_error_simplification (c q x I₀ I₁ : Rat) :
    c*q*(x*x*(I₀+c*I₁)+x*I₁)+q*x*I₀ =
      (c*q*x*x+q*x)*(I₀+c*I₁) := by grind

/-- Clearing denominators in the periodic error x^2/(2A)=N*u^2/2. -/
theorem periodic_error_simplification (a b N A x u : Rat)
    (hA : N*A=a*b) (hx : x*x=a*b*u*u) :
    x*x=N*A*u*u := by grind

#print axioms inward_factor_identity
#print axioms inward_factor_monotone
#print axioms inward_product_monotone
#print axioms inward_first_product_strict
#print axioms longer_product_monotone
#print axioms even_run_coefficient_identity
#print axioms free_adjacent_crossing
#print axioms free_adjacent_root_unique
#print axioms periodic_adjacent_crossing
#print axioms periodic_adjacent_root_unique
#print axioms free_error_simplification
#print axioms periodic_error_simplification
end Kagey131
