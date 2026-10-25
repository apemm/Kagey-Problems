import Mathlib

/-!
# Paper C2: vanishing on a graph

Paper C2 (`paperC2/sec_exactlaw.tex`), Lemma `lem:graph`. Let `P ∈ ℂ[s, w]` be irreducible and
monic in `s` of degree `d ≥ 1`, written as a polynomial in `s` over `ℂ[w] = MvPolynomial σ ℂ`. Let
`U ⊆ ℝ^σ` be nonempty and open and `θ` a function on `U` with `P(θ(w), w) = 0`. If `R ∈ ℂ[s, w]`
also vanishes at `(θ(w), w)` for all `w ∈ U`, then `P` divides `R`.

* `evalAt`: evaluation of a polynomial in `s` over `ℂ[w]` at `(θ(w), w)`;
* `mvPolynomial_eq_zero_of_open`: a complex polynomial in `w` that vanishes at all real points of
  a nonempty open set is zero;
* `graph_dvd`: the lemma. The proof follows the paper: divide by `P`, and if the remainder `B`
  is not zero, the resultant of `P` and `B` vanishes on `U` by the Bezout identity, hence is
  zero, hence `P` and `B` have a common factor over the fraction field of `ℂ[w]`, so `P` divides
  `B` by Gauss's lemma, which is impossible for `deg B < deg P`.
-/

namespace Kagey131.PaperC.C2

open Polynomial

variable {σ : Type*} [Finite σ]

/-- Evaluation of a polynomial in `s` over `ℂ[w]` at `(θ(w), w)`, for a real point `w`. -/
noncomputable def evalAt (θ : (σ → ℝ) → ℂ) (w : σ → ℝ) : (MvPolynomial σ ℂ)[X] →+* ℂ :=
  (Polynomial.evalRingHom (θ w)).comp
    (Polynomial.mapRingHom (MvPolynomial.eval (fun i => ((w i : ℝ) : ℂ))))

/-- A complex polynomial in `w` that vanishes at all real points of a nonempty open set is zero. -/
theorem mvPolynomial_eq_zero_of_open (ρ : MvPolynomial σ ℂ) (U : Set (σ → ℝ)) (hU : IsOpen U)
    (hne : U.Nonempty)
    (h : ∀ w ∈ U, MvPolynomial.eval (fun i => ((w i : ℝ) : ℂ)) ρ = 0) : ρ = 0 := by
  classical
  obtain ⟨w0, hw0⟩ := hne
  have := Fintype.ofFinite σ
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU w0 hw0
  let t : σ → Set ℝ := fun i => if i ∈ I then u i else Set.univ
  have ht_open : ∀ i, IsOpen (t i) := fun i => by
    by_cases hi : i ∈ I
    · simp only [t, hi, if_true]; exact (hu i hi).1
    · simp [t, hi]
  have ht_mem : ∀ i, w0 i ∈ t i := fun i => by
    by_cases hi : i ∈ I
    · simp only [t, hi, if_true]; exact (hu i hi).2
    · simp [t, hi]
  have ht_inf : ∀ i, (t i).Infinite := fun i =>
    infinite_of_mem_nhds (w0 i) ((ht_open i).mem_nhds (ht_mem i))
  have hsubU : Set.pi Set.univ t ⊆ U := by
    intro w hw
    apply hsub
    intro i hi
    have := hw i (Set.mem_univ i)
    rw [show t i = u i from if_pos hi] at this
    exact this
  let s : σ → Set ℂ := fun i => (fun x : ℝ => (x : ℂ)) '' t i
  refine MvPolynomial.funext_set s (fun i => (ht_inf i).image Complex.ofReal_injective.injOn) ?_
  intro x hx
  have hx' : ∀ i, ∃ y ∈ t i, (y : ℂ) = x i := fun i => hx i (Set.mem_univ i)
  choose y hy hyx using hx'
  have : (fun i => ((y i : ℝ) : ℂ)) = x := funext hyx
  rw [← this]
  simpa using h y (hsubU fun i _ => hy i)


/-- Gauss's lemma step: if a monic irreducible `P` is not coprime to `B` over the fraction field,
then `P` divides `B`. -/
theorem dvd_of_not_coprime {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] {P B : R[X]}
    (hirr : Irreducible P) (hm : P.Monic)
    (hnc : ¬ IsCoprime (P.map (algebraMap R K)) (B.map (algebraMap R K))) : P ∣ B := by
  have hirrK : Irreducible (P.map (algebraMap R K)) :=
    (hm.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hirr
  have hdvdK : P.map (algebraMap R K) ∣ B.map (algebraMap R K) := by
    by_contra hnd'
    exact hnc ((Irreducible.coprime_iff_not_dvd hirrK).mpr hnd')
  exact (hm.isPrimitive.dvd_iff_fraction_map_dvd_fraction_map K).mpr hdvdK

/-- Lemma `lem:graph`. -/
theorem graph_dvd {P R : (MvPolynomial σ ℂ)[X]} (hirr : Irreducible P) (hm : P.Monic)
    (hd : 0 < P.natDegree) (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (θ : (σ → ℝ) → ℂ) (hP : ∀ w ∈ U, evalAt θ w P = 0) (hR : ∀ w ∈ U, evalAt θ w R = 0) :
    P ∣ R := by
  classical
  by_contra hnd
  set B : (MvPolynomial σ ℂ)[X] := R %ₘ P with hBdef
  set A : (MvPolynomial σ ℂ)[X] := R /ₘ P with hAdef
  have hRB : B + P * A = R := modByMonic_add_div R P
  have hB0 : B ≠ 0 := fun h0 => hnd ((modByMonic_eq_zero_iff_dvd hm).mp h0)
  have hBdeg : B.degree < P.degree := degree_modByMonic_lt R hm
  have hBθ : ∀ w ∈ U, evalAt θ w B = 0 := by
    intro w hw
    have := hR w hw
    rw [← hRB, map_add, map_mul, hP w hw, zero_mul, add_zero] at this
    exact this
  have hBnat : B.natDegree < P.natDegree := natDegree_lt_natDegree hB0 hBdeg
  obtain ⟨p, q, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant P B (m := P.natDegree)
    (n := B.natDegree) le_rfl le_rfl (Or.inl hd.ne')
  set ρ : MvPolynomial σ ℂ := resultant P B P.natDegree B.natDegree with hρ
  have hρU : ∀ w ∈ U, MvPolynomial.eval (fun i => ((w i : ℝ) : ℂ)) ρ = 0 := by
    intro w hw
    have := congrArg (evalAt θ w) e
    rw [map_add, map_mul, map_mul, hP w hw, hBθ w hw, zero_mul, zero_mul, add_zero] at this
    simpa [evalAt] using this.symm
  have hρ0 : ρ = 0 := mvPolynomial_eq_zero_of_open ρ U hU hne hρU
  have hφ : Function.Injective (algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))) :=
    IsFractionRing.injective _ _
  have hres : resultant (P.map (algebraMap _ (FractionRing (MvPolynomial σ ℂ))))
      (B.map (algebraMap _ (FractionRing (MvPolynomial σ ℂ)))) = 0 := by
    rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ,
      resultant_map_map, ← hρ, hρ0, map_zero]
  have hnc := (resultant_eq_zero_iff.mp hres).2
  have hdvd : P ∣ B := dvd_of_not_coprime (FractionRing (MvPolynomial σ ℂ)) hirr hm hnc
  obtain ⟨T, hT⟩ := hdvd
  have hT0 : T ≠ 0 := fun h0 => hB0 (by rw [hT, h0, mul_zero])
  have := hm.natDegree_mul' hT0
  rw [← hT] at this
  omega

end Kagey131.PaperC.C2
