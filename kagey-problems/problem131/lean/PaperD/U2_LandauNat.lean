import PaperD.U2_LandauLocal

/-!
# Paper D, Theorem 3.9: `ℕ`-indexed interface (matching track U1's `CPN`, `law`, `CPCharHyp`)

Track U1 indexes the laws `f_N = law ε N` and `CP_N = CPN N x` by `m : ℕ`, and its classical
hypothesis `CPCharHyp` gives the characteristic function of `CP_N` in the form
`HasSum (fun m => CP_N(m) e^{iθm}) (exp (∑_{d=1}^{N-1} (x/(d(d+1))) (e^{iθd} - 1)))`.
This module restates Theorem 3.9(a), (b) for `ℕ`-indexed laws in exactly that form:

* `CPCharFunNat N x p` : the U1 form of "`p` has characteristic function `e^{xΨ_N}`"
  (`eI θ d` of U1 is `cexp (((θ * d : ℝ) : ℂ) * I)`, `cpRate x d = x/(d(d+1))`);
* `extZ` : extension of an `ℕ`-indexed law by `0` to `ℤ`;
* `landau_local_cp_nat`, `landau_local_fN_nat` : Theorem 3.9(a), (b) for `m : ℕ`.
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology
open scoped Real

noncomputable section

/-- Extension of an `ℕ`-indexed sequence by `0` on the negative integers. -/
def extZ (f : ℕ → ℝ) : ℤ → ℝ
  | Int.ofNat n => f n
  | Int.negSucc _ => 0

@[simp] lemma extZ_natCast (f : ℕ → ℝ) (n : ℕ) : extZ f (n : ℤ) = f n := rfl

@[simp] lemma extZ_neg_succ (f : ℕ → ℝ) (n : ℕ) : extZ f (-((n : ℤ) + 1)) = 0 := rfl

lemma extZ_of_neg (f : ℕ → ℝ) {m : ℤ} (hm : m < 0) : extZ f m = 0 := by
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_lt hm)
  rcases n with _ | n
  · simp at hm
  · exact extZ_neg_succ f n

/-- **U1 form** of "`p : ℕ → ℝ` has the characteristic function `e^{xΨ_N(θ)}`":
`∑_m p(m) e^{iθm} = exp(∑_{d=1}^{N-1} (x/(d(d+1)))(e^{iθd} - 1))` (as a `HasSum`). This is what
U1's classical hypothesis `CPCharHyp` gives for `p = CPN N x`. -/
def CPCharFunNat (N : ℕ) (x : ℝ) (p : ℕ → ℝ) : Prop :=
  ∀ θ : ℝ, HasSum (fun m : ℕ => ((p m : ℝ) : ℂ) * cexp (((θ * m : ℝ) : ℂ) * I))
    (cexp (∑ d ∈ Icc 1 (N - 1), ((x / ((d : ℝ) * ((d : ℝ) + 1)) : ℝ) : ℂ)
      * (cexp (((θ * d : ℝ) : ℂ) * I) - 1)))

/-- The exponent of `CPCharFunNat` is `xΨ_N(θ)`. -/
lemma cp_exponent_eq (N : ℕ) (x θ : ℝ) :
    ∑ d ∈ Icc 1 (N - 1), ((x / ((d : ℝ) * ((d : ℝ) + 1)) : ℝ) : ℂ)
      * (cexp (((θ * d : ℝ) : ℂ) * I) - 1) = (x : ℂ) * psiN N θ := by
  unfold psiN
  rw [Finset.mul_sum]
  have hsub : Icc 1 (N - 1) ⊆ range N := by
    intro d hd; rw [mem_Icc] at hd; rw [mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold psiTerm
    push_cast
    ring
  · intro d hd hnot
    have : d = 0 := by
      rw [mem_range] at hd; rw [mem_Icc] at hnot; omega
    subst this
    unfold psiTerm; simp

/-- From the U1 form to the `ℤ` form used in `U2_LandauLocal`. -/
lemma cpCharFun_extZ {N : ℕ} {x : ℝ} {p : ℕ → ℝ} (hp0 : ∀ m, 0 ≤ p m)
    (hchar : CPCharFunNat N x p) :
    Summable (fun k => |extZ p k|) ∧ CPCharFun N x (extZ p) := by
  -- summability from `θ = 0`
  have h0 := hchar 0
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one, sub_self, mul_zero,
    Finset.sum_const_zero] at h0
  have hpsum : HasSum p 1 := by
    have h0' : HasSum (fun m => ((p m : ℝ) : ℂ)) ((1 : ℝ) : ℂ) := by simpa using h0
    exact Complex.hasSum_ofReal.mp h0'
  have hpos : HasSum (fun n : ℕ => |extZ p (n : ℤ)|) 1 := by
    have e : (fun n : ℕ => |extZ p (n : ℤ)|) = p := by
      funext n; rw [extZ_natCast, abs_of_nonneg (hp0 n)]
    rw [e]; exact hpsum
  have hneg : HasSum (fun n : ℕ => |extZ p (-((n : ℤ) + 1))|) 0 := by
    have e : (fun n : ℕ => |extZ p (-((n : ℤ) + 1))|) = fun _ => 0 := by
      funext n; rw [extZ_neg_succ, abs_zero]
    rw [e]; exact hasSum_zero
  refine ⟨(HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => |extZ p k|) hpos hneg).summable,
    fun θ => ?_⟩
  have hpos' : HasSum (fun n : ℕ => ((extZ p (n : ℤ) : ℝ) : ℂ) * cexp (((((n : ℤ) : ℝ)) * θ : ℝ) * I))
      (cexp ((x : ℂ) * psiN N θ)) := by
    have e : (fun n : ℕ => ((extZ p (n : ℤ) : ℝ) : ℂ) * cexp (((((n : ℤ) : ℝ)) * θ : ℝ) * I))
        = fun m : ℕ => ((p m : ℝ) : ℂ) * cexp (((θ * m : ℝ) : ℂ) * I) := by
      funext n; rw [extZ_natCast, Int.cast_natCast, mul_comm (n : ℝ) θ]
    rw [e, ← cp_exponent_eq]
    exact hchar θ
  have hneg' : HasSum (fun n : ℕ => ((extZ p (-((n : ℤ) + 1)) : ℝ) : ℂ)
      * cexp (((((-((n : ℤ) + 1)) : ℤ) : ℝ) * θ : ℝ) * I)) 0 := by
    have e : (fun n : ℕ => ((extZ p (-((n : ℤ) + 1)) : ℝ) : ℂ)
        * cexp (((((-((n : ℤ) + 1)) : ℤ) : ℝ) * θ : ℝ) * I)) = fun _ => 0 := by
      funext n; rw [extZ_neg_succ, Complex.ofReal_zero, zero_mul]
    rw [e]; exact hasSum_zero
  have := HasSum.of_nat_of_neg_add_one
    (f := fun k : ℤ => ((extZ p k : ℝ) : ℂ) * cexp ((((k : ℝ) * θ : ℝ) : ℂ) * I)) hpos' hneg'
  rw [add_zero] at this
  exact this.tsum_eq

/-- **Theorem 3.9(a)** for `ℕ`-indexed `CP_N` (U1's `CPN N x`): assume lattice Fourier inversion;
let `x ≥ 1`, `4x ≤ N`, `p ≥ 0` with characteristic function `e^{xΨ_N}` (U1 form). Then for every
`m : ℕ`, `|x p(m) - f_L(λ_m)| ≤ 3600((1 + log x)/x + x/N)`. -/
theorem landau_local_cp_nat (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ p m) (hchar : CPCharFunNat N x p) (m : ℕ) :
    ‖((x * p m : ℝ) : ℂ) - landauDensity (lamm x m)‖ ≤ 3600 * ((1 + Real.log x) / x + x / N) := by
  obtain ⟨hs, hc⟩ := cpCharFun_extZ hp0 hchar
  simpa using landau_local_cp hInv hx hxN (extZ p) hs hc (m : ℤ)

/-- **Theorem 3.9(b)** for `ℕ`-indexed laws: if moreover `|f(m) - p(m)| ≤ δ`, then
`|x f(m) - f_L(λ_m)| ≤ 3600((1+log x)/x + x/N) + xδ`. -/
theorem landau_local_fN_nat (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ p m) (hchar : CPCharFunNat N x p)
    (f : ℕ → ℝ) {δ : ℝ} (m : ℕ) (hcp : |f m - p m| ≤ δ) :
    ‖((x * f m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ 3600 * ((1 + Real.log x) / x + x / N) + x * δ := by
  obtain ⟨hs, hc⟩ := cpCharFun_extZ hp0 hchar
  have := landau_local_fN hInv hx hxN (extZ p) hs hc (extZ f) (m : ℤ) (by simpa using hcp)
  simpa using this

/-- **The conclusion of Theorem 3.8** (`thm:cp`) in U1's indexing: for every `m : ℕ`,
`|f_N(m) - CP_N(m)| ≤ δ_B` (U1: `f = law ε N`, `p = CPN N (N*ε)`). -/
def ThmCPConclusionNat (N : ℕ) (ε : ℝ) (f p : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, |f m - p m| ≤ deltaB N ε

/-- **Theorem 3.9(b)** with `δ_B`, in U1's indexing: assume (H) (we use only `x = Nε ≥ 1` and
`ε ≤ 1/4`), lattice Fourier inversion, the characteristic function of `CP_N` (U1 form) and the
conclusion of Theorem 3.8. Then for every `m : ℕ`,
`|x f_N(m) - f_L(λ_m)| ≤ 3600((1+log x)/x + x/N) + x δ_B`. -/
theorem landau_local_fN_of_thmCP_nat (hInv : LatticeFourierInversionHyp) {N : ℕ} {ε : ℝ}
    (hε : ε ≤ 1 / 4) (hx : 1 ≤ (N : ℝ) * ε) (p : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ p m)
    (hchar : CPCharFunNat N ((N : ℝ) * ε) p) (f : ℕ → ℝ) (hcp : ThmCPConclusionNat N ε f p)
    (m : ℕ) :
    ‖(((N * ε) * f m : ℝ) : ℂ) - landauDensity (lamm (N * ε) m)‖
      ≤ 3600 * ((1 + Real.log (N * ε)) / (N * ε) + (N * ε) / N) + (N * ε) * deltaB N ε := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hxN : 4 * ((N : ℝ) * ε) ≤ N := by nlinarith
  exact landau_local_fN_nat hInv hx hxN p hp0 hchar f m (hcp m)

end

end Kagey131.PaperD.U2
