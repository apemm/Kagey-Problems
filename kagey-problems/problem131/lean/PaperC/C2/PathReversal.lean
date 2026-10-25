import Mathlib
import PaperC.ChainLaw
import PaperC.C2.TimeReversal

/-!
# Paper C2: path reversal from the stationary start

Paper C2 (`paperC2/sec_minors.tex`), Remark `rem:stationary`. With the start `π`, the law of the
composition of the chain of `PaperC.ChainLaw` is the same under `Q` and under the time reversal
`Q*`, for every `N` and every step `h`, and so is the weighted law.

The chain has off-diagonal rates `a`, exit rates `q` and transition matrix
`P(x,x) = 1 - h q_x`, `P(x,y) = h a_xy` (`stepP`). The time reversal has the same exit rates and
the off-diagonal rates `aRev π a i j = π_j a_ji / π_i`, that is `P* = D_π⁻¹ Pᵀ D_π`.

* `aRev_eq_starMat`: for a matrix `Q` with off-diagonal part `a`, `aRev` is `Q*` off the diagonal;
* `aRev_exit`: if `π_x q_x = ∑_{y ≠ x} π_y a_yx` (stationarity of `π`), the exit rates of the
  reversed chain are again `q`, so `P*` is stochastic when `P` is (`sum_stepP` of `ChainLaw`);
* `wordWt_reverse`: `π_{x_1} ∏ P(x_t, x_{t+1}) = π_{x_N} ∏ P*(x_{t+1}, x_t)`, that is
  `wordWt π (aRev π a) q h w.reverse = wordWt π a q h w`, for every `π > 0`; stationarity of `π`
  is not needed for the identity, only for `P*` to be stochastic;
* `lawP_aRev`: the law of the composition from the start `π` is the same under `a` and `aRev π a`,
  for every `N` and `h`;
* `lawP_aRev_weighted`: the same for the law weighted by any function of the counts, such as
  `e^{T v·n/N}`.
-/

namespace Kagey131.PaperC.C2

open Finset Kagey131.PaperC

variable {d : ℕ}

/-- The off-diagonal rates of the time reversal, `π_j a_ji / π_i`. -/
noncomputable def aRev (π : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (i j : Fin d) : ℝ :=
  π j * a j i / π i

/-- Off the diagonal, `aRev` is the time reversal `Q*` of `GeneratorFiber` and `TimeReversal`. -/
theorem aRev_eq_starMat (π : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    aRev π (fun x y => Q x y) i j = starMat π Q i j := rfl

/-- If `π` is stationary, `π_x q_x = ∑_{y ≠ x} π_y a_yx`, the reversed chain has the exit
rates `q`. -/
theorem aRev_exit {π : Fin d → ℝ} (hπ : ∀ i, 0 < π i) {a : Fin d → Fin d → ℝ} {q : Fin d → ℝ}
    (hstat : ∀ x, π x * q x = ∑ y ∈ univ.erase x, π y * a y x) (x : Fin d) :
    q x = ∑ y ∈ univ.erase x, aRev π a x y := by
  have hx := (hπ x).ne'
  unfold aRev
  rw [← sum_div, ← hstat x]
  field_simp

/-- The product of `f` along consecutive entries of a path. -/
def adjWt (f : Fin d → Fin d → ℝ) : List (Fin d) → ℝ
  | [] => 1
  | [_] => 1
  | x :: y :: l => f x y * adjWt f (y :: l)

/-- The last state of the path `x :: l`. -/
def lastOf : Fin d → List (Fin d) → Fin d
  | x, [] => x
  | _, y :: l => lastOf y l

theorem chainWt_eq_adjWt (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (x : Fin d)
    (l : List (Fin d)) : chainWt a q h x l = adjWt (stepP a q h) (x :: l) := by
  induction l generalizing x with
  | nil => simp [chainWt, adjWt]
  | cons y l ih => simp only [chainWt, adjWt, ih]

theorem reverse_cons_eq (x : Fin d) (l : List (Fin d)) :
    ∃ t, (x :: l).reverse = lastOf x l :: t := by
  induction l generalizing x with
  | nil => exact ⟨[], rfl⟩
  | cons y l ih =>
    obtain ⟨t, ht⟩ := ih y
    refine ⟨t ++ [x], ?_⟩
    rw [List.reverse_cons, ht]
    rfl

theorem adjWt_append_singleton (f : Fin d → Fin d → ℝ) (y : Fin d) (u : List (Fin d)) (z : Fin d) :
    adjWt f ((y :: u) ++ [z]) = adjWt f (y :: u) * f (lastOf y u) z := by
  induction u generalizing y with
  | nil => simp [adjWt, lastOf]
  | cons y' u ih =>
    have := ih y'
    simp only [List.cons_append] at this ⊢
    rw [adjWt, this, adjWt, lastOf]
    ring

theorem lastOf_of_reverse {x z : Fin d} {l t : List (Fin d)} (h : (x :: l).reverse = z :: t) :
    lastOf z t = x := by
  obtain ⟨t', ht'⟩ := reverse_cons_eq z t
  have h1 : (z :: t).reverse = x :: l := by rw [← h, List.reverse_reverse]
  rw [h1] at ht'
  exact (List.cons.inj ht').1.symm

/-- Reversing a path flips the arguments of `f`. -/
theorem adjWt_reverse (f : Fin d → Fin d → ℝ) (x : Fin d) (l : List (Fin d)) :
    adjWt f (x :: l).reverse = adjWt (fun a b => f b a) (x :: l) := by
  induction l generalizing x with
  | nil => simp [adjWt]
  | cons y l ih =>
    obtain ⟨t, ht⟩ := reverse_cons_eq y l
    have hrev : (x :: y :: l).reverse = (lastOf y l :: t) ++ [x] := by
      rw [List.reverse_cons, ht]
    rw [hrev, adjWt_append_singleton, lastOf_of_reverse ht, ← ht, ih]
    simp only [adjWt]
    ring

/-- Telescoping of a detailed-balance factor: if `g x y = π_x f x y / π_y`, then
`adjWt g (x :: l) · π_last = π_x · adjWt f (x :: l)`. -/
theorem adjWt_balance {π : Fin d → ℝ} (hπ : ∀ i, 0 < π i) (f g : Fin d → Fin d → ℝ)
    (hg : ∀ x y, g x y = π x * f x y / π y) (x : Fin d) (l : List (Fin d)) :
    adjWt g (x :: l) * π (lastOf x l) = π x * adjWt f (x :: l) := by
  induction l generalizing x with
  | nil => simp [adjWt, lastOf]
  | cons y l ih =>
    have ih' := ih y
    rw [adjWt, adjWt, lastOf, hg]
    have hy := (hπ y).ne'
    calc π x * f x y / π y * adjWt g (y :: l) * π (lastOf y l)
        = π x * f x y / π y * (adjWt g (y :: l) * π (lastOf y l)) := by ring
      _ = π x * (f x y * adjWt f (y :: l)) := by rw [ih']; field_simp

/-- Detailed balance of the transition probabilities: `P*(y, x) = π_x P(x, y) / π_y`. -/
theorem stepP_aRev {π : Fin d → ℝ} (hπ : ∀ i, 0 < π i) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ)
    (h : ℝ) (x y : Fin d) :
    stepP (aRev π a) q h y x = π x * stepP a q h x y / π y := by
  have hy := (hπ y).ne'
  by_cases hxy : x = y
  · subst hxy
    simp [stepP]
    field_simp
  · have hyx : y ≠ x := Ne.symm hxy
    simp [stepP, hxy, hyx, aRev]
    field_simp

/-- Path reversal, `rem:stationary`: `π_{x_1} ∏ P(x_t, x_{t+1}) = π_{x_N} ∏ P*(x_{t+1}, x_t)`.
For every positive `π`, the path probability from the start `π` of the reversed path under the
reversed chain equals that of the path under the chain. -/
theorem wordWt_reverse {π : Fin d → ℝ} (hπ : ∀ i, 0 < π i) (a : Fin d → Fin d → ℝ)
    (q : Fin d → ℝ) (h : ℝ) (w : List (Fin d)) :
    wordWt π (aRev π a) q h w.reverse = wordWt π a q h w := by
  cases w with
  | nil => simp [wordWt]
  | cons x l =>
    obtain ⟨t, ht⟩ := reverse_cons_eq x l
    have h1 := adjWt_balance hπ (stepP a q h) (fun x y => stepP (aRev π a) q h y x)
      (fun x y => stepP_aRev hπ a q h x y) x l
    rw [ht]
    simp only [wordWt]
    rw [chainWt_eq_adjWt, ← ht, adjWt_reverse, chainWt_eq_adjWt]
    rw [← h1]
    ring

/-- Rem `rem:stationary`: with the start `π`, the law of the composition is the same under the
chain and under its time reversal, for every `N` and every step `h`. Reversal is a bijection of
the paths of length `N` that keeps the counts. -/
theorem lawP_aRev {π : Fin d → ℝ} (hπ : ∀ i, 0 < π i) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ)
    (h : ℝ) (N : ℕ) (n : Fin d → ℕ) :
    lawP π (aRev π a) q h N n = lawP π a q h N n := by
  unfold lawP
  refine Finset.sum_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_words] at hw ⊢
    refine ⟨by simpa using hw.1, ?_⟩
    rw [← hw.2]
    funext i
    simp [occ]
  · intro w hw
    simp only [mem_filter, mem_words] at hw ⊢
    refine ⟨by simpa using hw.1, ?_⟩
    rw [← hw.2]
    funext i
    simp [occ]
  · intro w _; simp
  · intro w _; simp
  · intro w _
    have := wordWt_reverse hπ a q h w.reverse
    rw [List.reverse_reverse] at this
    exact this

/-- The same for the law weighted by any function of the counts (such as `e^{T v·n/N}`):
the weighted law `P_N(n) e^{T v·n/N}` is the same under `Q` and `Q*`, for every field `v`. -/
theorem lawP_aRev_weighted {π : Fin d → ℝ} (hπ : ∀ i, 0 < π i) (a : Fin d → Fin d → ℝ)
    (q : Fin d → ℝ) (h : ℝ) (N : ℕ) (g : (Fin d → ℕ) → ℝ) (n : Fin d → ℕ) :
    lawP π (aRev π a) q h N n * g n = lawP π a q h N n * g n := by
  rw [lawP_aRev hπ]

end Kagey131.PaperC.C2
