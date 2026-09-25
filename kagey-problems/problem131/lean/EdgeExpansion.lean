import Std
/-!
Algebra of the fixed-edge root expansion for Problem 131.
This Lean verification code was generated with Claude Opus 5.5.
The analytic implicit-function theorem and Taylor expansion hypotheses are
not proved here. These results verify the exact deductions from their first
and second coefficient equations, including the universal correction -1.
-/
namespace Kagey131

/-- The first Taylor coefficient of y=b*u^2 at the crossing is -2c. -/
theorem edge_first_coefficient (c h d₁ : Rat) (hh : h≠0)
    (heq : h*d₁+2*c*h=0) : d₁ = -2*c := by
  have hf : h*(d₁+2*c)=0 := by grind
  rcases Rat.mul_eq_zero.mp hf with h0|h0 <;> grind

/-- Converting y=c^2+d1*epsilon+... to u=epsilon*sqrt(y)
forces the coefficient of epsilon^2 to be -1, independent of the bin. -/
theorem universal_edge_correction (c h d₁ α : Rat) (hc : c≠0) (hh : h≠0)
    (hfirst : h*d₁+2*c*h=0) (hsqrt : d₁=2*c*α) : α = -1 := by
  have hd := edge_first_coefficient c h d₁ hh hfirst
  have hf : c*(α+1)=0 := by grind
  rcases Rat.mul_eq_zero.mp hf with h0|h0 <;> grind

/-- The second Taylor coefficient equation, with a denominator c cleared. -/
def EdgeSecondEquation (c y h j d₁ d₂ : Rat) : Prop :=
  c*h*d₂+c*j*d₁*d₁/2+(h+2*c*c*j)*d₁+
    c*((y-y*y/2)*j-y*h)=0

/-- The exact second coefficient of y, written without divisions by H'. -/
theorem edge_second_coefficient (c y h j d₁ d₂ : Rat) (hc : c≠0) (hh : h≠0)
    (hy : y=c*c) (hfirst : h*d₁+2*c*h=0)
    (hsecond : EdgeSecondEquation c y h j d₁ d₂) :
    h*(d₂-2-y)=(y+y*y/2)*j := by
  have hd := edge_first_coefficient c h d₁ hh hfirst
  unfold EdgeSecondEquation at hsecond
  have hf : c*(h*(d₂-2-y)-(y+y*y/2)*j)=0 := by grind
  rcases Rat.mul_eq_zero.mp hf with h0|h0 <;> grind

/-- Exact algebraic verification of the third-order coefficient gamma.
Here h=H'(y), j=H''(y), c^2=y, and d2=1+2c*gamma. -/
theorem edge_third_coefficient (c y h j d₁ d₂ γ : Rat) (hc : c≠0) (hh : h≠0)
    (hy : y=c*c) (hfirst : h*d₁+2*c*h=0)
    (hsecond : EdgeSecondEquation c y h j d₁ d₂)
    (hsqrt : d₂=1+2*c*γ) :
    2*c*h*γ=(1+y)*h+(y+y*y/2)*j := by
  have hd := edge_second_coefficient c y h j d₁ d₂ hc hh hy hfirst hsecond
  grind

/-- Converting switching odds u to switching probability u/(1+u)
changes the second coefficient from alpha to alpha-c^2. -/
theorem odds_to_probability_second_coefficient (c α β : Rat)
    (heq : β+c*c=α) : β=α-c*c := by grind

/-- The probability correction corresponding to the universal odds correction. -/
theorem edge_probability_correction (c h d₁ α β : Rat) (hc : c≠0) (hh : h≠0)
    (hfirst : h*d₁+2*c*h=0) (hsqrt : d₁=2*c*α)
    (hconversion : β+c*c=α) : β= -(1+c*c) := by
  have ha := universal_edge_correction c h d₁ α hc hh hfirst hsqrt
  grind

#print axioms edge_first_coefficient
#print axioms universal_edge_correction
#print axioms edge_second_coefficient
#print axioms edge_third_coefficient
#print axioms odds_to_probability_second_coefficient
#print axioms edge_probability_correction
end Kagey131
