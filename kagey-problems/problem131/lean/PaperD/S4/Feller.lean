import PaperD.FL1_Urn

/-!
# The coin-turning note: the Feller coupling of `rem:aging-feller`

`rem:aging-feller` says that the multiset of the spacings between the successes of independent
trials with success probabilities `f_t = α/(α+t-1)` has the same law as the multiset of the table
sizes of the Chinese restaurant process with parameter `α = dθ`, for a fixed number `T` of trials
or customers. Here both laws are computed and shown equal to the Ewens sampling formula
`ESF = T!/α^{(T)} ∏_j (α/j)^{c_j}/c_j!`, where `c_j` is the number of parts equal to `j`.

* The spacing side (`spLaw`): the runs of the trials are a list `l` of positive lengths with sum
  `T` (the first trial is a success since `f_1 = 1`, and a run is a success followed by
  failures). `runProb α 1 l` is the probability of the runs `l` for independent trials. The law
  of the multiset `m` is the sum over the distinct orderings `l` of `m`. `runProb_closed` shows
  `runProb α 1 l = α^k T!/(α^{(T)} ∏ (partial sums of l))`, and the sum over orderings of the
  reciprocal of the product of partial sums is `1/(∏ m · ∏ c_j!)` (`orderingSum`).
* The restaurant side (`crpLaw`): the chain of the multiset of table sizes, a new table with
  probability `α/(α+T)` and a table of size `n` grown with probability `n/(α+T)` each, written as
  the forward equation through the predecessors of a multiset. `crpLaw_eq_esf` proves the law is
  the Ewens formula by induction on `T`.
* `feller_coupling`: the two laws are equal, for every `T`, every `α > 0` and every multiset `m`
  of positive integers with sum `T`.
-/

namespace Kagey131.PaperD.S4

open Finset Kagey131.PaperF.FL1

/-! ## The spacing side -/

/-- The success probability of trial `t`: `f_t = α/(α+t-1)`. -/
noncomputable def fT (α : ℝ) (t : ℕ) : ℝ := α / (α + t - 1)

/-- The probability that independent trials `s, s+1, …` (success probabilities `fT α t`) split
into the runs of lengths `l`: a success at the first trial of each run and failures at the other
trials of the run. -/
noncomputable def runProb (α : ℝ) : ℕ → List ℕ → ℝ
  | _, [] => 1
  | s, x :: r => fT α s * (∏ u ∈ range (x - 1), (1 - fT α (s + 1 + u))) * runProb α (s + x) r

/-- The product of the partial sums of `l`, with the partial sums counted from the offset
`s - 1`: `Dp s [x₁, x₂, …] = (s+x₁-1) (s+x₁+x₂-1) ⋯`. -/
def Dp : ℕ → List ℕ → ℕ
  | _, [] => 1
  | s, x :: r => (s + x - 1) * Dp (s + x) r

theorem fail_prod {α : ℝ} (hα : 0 < α) {s : ℕ} (hs : 1 ≤ s) (y : ℕ) :
    ∏ u ∈ range y, (1 - fT α (s + 1 + u)) = rpoch s y / rpoch (α + s) y := by
  induction y with
  | zero => simp [rpoch]
  | succ y ih =>
    rw [prod_range_succ, ih, rpoch_succ, rpoch_succ]
    have h1 : 0 < rpoch (α + s) y := rpoch_pos (by positivity) y
    have h2 : 0 < α + s + y := by positivity
    have e : 1 - fT α (s + 1 + y) = (s + y) / (α + s + y) := by
      unfold fT
      push_cast
      have : α + (s + 1 + y) - 1 = α + s + y := by ring
      rw [this]
      field_simp
      ring
    rw [e]
    field_simp

/-- The weight of one run of length `x ≥ 1` starting at trial `s ≥ 1`. -/
theorem block_weight {α : ℝ} (hα : 0 < α) {s : ℕ} (hs : 1 ≤ s) {x : ℕ} (hx : 1 ≤ x) :
    fT α s * ∏ u ∈ range (x - 1), (1 - fT α (s + 1 + u)) =
      α * rpoch s (x - 1) / rpoch (α + s - 1) x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [Nat.add_sub_cancel, fail_prod hα hs]
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have e : rpoch (α + s - 1) (y + 1) = (α + s - 1) * rpoch (α + s) y := by
    have := rpoch_add (α + s - 1) 1 y
    rw [show y + 1 = 1 + y by ring, this]
    simp only [rpoch, prod_range_one, Nat.cast_zero, add_zero]
    rw [show α + s - 1 + (1 : ℕ) = α + s by push_cast; ring]
  rw [e]
  unfold fT
  have h1 : 0 < rpoch (α + s) y := rpoch_pos (by positivity) y
  have h2 : 0 < α + s - 1 := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  field_simp

/-- The closed form of the run probability: for `s ≥ 1`, positive parts, and total `S`,
`runProb α s l · α^{(S)}_{shifted} · Dp s l · (s-1)! = α^k (s+S-1)!`, where the shifted rising
factorial is `(α+s-1)^{(S)}`. -/
theorem runProb_closed {α : ℝ} (hα : 0 < α) (l : List ℕ) (hl : ∀ x ∈ l, 0 < x) :
    ∀ s : ℕ, 1 ≤ s →
      runProb α s l * (rpoch (α + s - 1) l.sum * (Dp s l : ℝ)) * ((s - 1).factorial : ℝ) =
        α ^ l.length * (((s + l.sum - 1).factorial : ℕ) : ℝ) := by
  induction l with
  | nil =>
    intro s hs
    simp [runProb, Dp, rpoch]
  | cons x r ih =>
    intro s hs
    have hx : 0 < x := hl x (by simp)
    have hr : ∀ y ∈ r, 0 < y := fun y hy => hl y (by simp [hy])
    have ih' := ih hr (s + x) (by omega)
    simp only [runProb, List.sum_cons, List.length_cons, Dp]
    rw [block_weight hα hs hx]
    have hrp : 0 < rpoch (α + s - 1) x := rpoch_pos (by
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs
      linarith) x
    -- rising factorial identities
    have hsplit : rpoch (α + s - 1) (x + r.sum) = rpoch (α + s - 1) x * rpoch (α + ((s + x : ℕ) : ℝ) - 1) r.sum := by
      rw [rpoch_add]
      congr 2
      push_cast; ring
    obtain ⟨e, rfl⟩ : ∃ e, s = e + 1 := ⟨s - 1, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    have hf : rpoch ((e : ℝ) + 1) y * (e.factorial : ℝ) = ((y + e).factorial : ℝ) :=
      rpoch_nat_mul_factorial e y
    have hfac : ((e + 1 + (y + 1) - 1).factorial : ℝ) = ((e + y + 1 : ℕ) : ℝ) * ((y + e).factorial : ℝ) := by
      rw [show e + 1 + (y + 1) - 1 = (y + e) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    have e1 : e + 1 + (y + 1 + r.sum) - 1 = e + 1 + (y + 1) + r.sum - 1 := by omega
    have e2 : e + 1 + (y + 1) - 1 = e + y + 1 := by omega
    rw [hsplit, e1]
    rw [e2] at ih' hfac
    simp only [Nat.add_sub_cancel, e2, Nat.cast_mul]
    have hcast : ((e + 1 : ℕ) : ℝ) = (e : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hrp hsplit ⊢
    set R := runProb α (e + 1 + (y + 1)) r with hR
    set ρ' := rpoch (α + ((e + 1 + (y + 1) : ℕ) : ℝ) - 1) r.sum with hρ'
    set ρx := rpoch (α + ((e : ℝ) + 1) - 1) (y + 1) with hρx
    set Dd := (Dp (e + 1 + (y + 1)) r : ℝ) with hDd
    have key : α * rpoch ((e : ℝ) + 1) y / ρx * R * (ρx * ρ' * (((e + y + 1 : ℕ) : ℝ) * Dd)) *
        (e.factorial : ℝ) =
        α * (rpoch ((e : ℝ) + 1) y * (e.factorial : ℝ)) * ((e + y + 1 : ℕ) : ℝ) * (R * (ρ' * Dd)) := by
      field_simp
    rw [key, hf]
    calc α * ((y + e).factorial : ℝ) * ((e + y + 1 : ℕ) : ℝ) * (R * (ρ' * Dd))
        = α * (R * (ρ' * Dd) * ((e + y + 1).factorial : ℝ)) := by rw [hfac]; ring
      _ = α ^ (r.length + 1) * ((e + 1 + (y + 1) + r.sum - 1).factorial : ℝ) := by
        rw [ih']; ring

/-! ## Orderings of a multiset -/

/-- The distinct orderings of a multiset, as a finite set of lists. -/
noncomputable def ordL (m : Multiset ℕ) : Finset (List ℕ) := (Multiset.lists m).toFinset

theorem mem_ordL {m : Multiset ℕ} {l : List ℕ} : l ∈ ordL m ↔ (l : Multiset ℕ) = m := by
  simp [ordL, Multiset.mem_lists_iff, eq_comm]

/-- `∏_j (count j m)!`, the product of the factorials of the multiplicities. -/
def cfact (m : Multiset ℕ) : ℕ := ∏ j ∈ m.toFinset, (m.count j).factorial

theorem cfact_cons (x : ℕ) (m : Multiset ℕ) : cfact (x ::ₘ m) = cfact m * (m.count x + 1) := by
  classical
  unfold cfact
  set s := insert x m.toFinset with hs
  have h1 : (x ::ₘ m).toFinset = s := by simp [hs]
  have hsub : m.toFinset ⊆ s := by intro a ha; simp [hs, ha]
  rw [h1, Finset.prod_subset hsub (f := fun j => (m.count j).factorial) (fun a _ ha => by
    rw [Multiset.count_eq_zero.mpr (fun h => ha (Multiset.mem_toFinset.mpr h))]; rfl)]
  rw [← Finset.mul_prod_erase s (fun j => ((x ::ₘ m).count j).factorial) (Finset.mem_insert_self x _),
    ← Finset.mul_prod_erase s (fun j => (m.count j).factorial) (Finset.mem_insert_self x _)]
  have : ∀ j ∈ s.erase x, ((x ::ₘ m).count j).factorial = (m.count j).factorial := by
    intro j hj
    rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl this, Multiset.count_cons_self, Nat.factorial_succ]
  ring

theorem cfact_erase {x : ℕ} {m : Multiset ℕ} (hx : x ∈ m) :
    cfact m = cfact (m.erase x) * m.count x := by
  conv_lhs => rw [← Multiset.cons_erase hx]
  rw [cfact_cons]
  congr 1
  have := Multiset.count_cons_self x (m.erase x)
  rw [Multiset.cons_erase hx] at this
  omega

theorem Dp_append (x : ℕ) (l : List ℕ) : ∀ s, Dp s (l ++ [x]) = Dp s l * (s + l.sum + x - 1) := by
  induction l with
  | nil => intro s; simp [Dp]
  | cons y r ih =>
    intro s
    simp only [List.cons_append, Dp, ih, List.sum_cons]
    have : s + y + r.sum + x - 1 = s + (y + r.sum) + x - 1 := by omega
    rw [this]; ring

theorem sum_ordL (m : Multiset ℕ) (hm : m ≠ 0) (F : List ℕ → ℝ) :
    ∑ l ∈ ordL m, F l = ∑ x ∈ m.toFinset, ∑ l ∈ ordL (m.erase x), F (l ++ [x]) := by
  classical
  rw [Finset.sum_sigma' m.toFinset (fun x => ordL (m.erase x)) (fun x l => F (l ++ [x]))]
  refine Finset.sum_nbij' (fun l => (⟨l.getLastD 0, l.dropLast⟩ : Σ _ : ℕ, List ℕ))
    (fun p => p.2 ++ [p.1]) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [mem_ordL] at hl
    have hne : l ≠ [] := by rintro rfl; simp at hl; exact hm hl.symm
    have hlast : l.getLastD 0 = l.getLast hne := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
    have hl' : (l : Multiset ℕ) = (l.getLast hne) ::ₘ ((l.dropLast : List ℕ) : Multiset ℕ) := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      simp [Multiset.cons_coe]
    simp only [Finset.mem_sigma, Multiset.mem_toFinset, mem_ordL, hlast]
    refine ⟨?_, ?_⟩
    · rw [← hl]; exact List.getLast_mem hne
    · rw [← hl, hl', Multiset.erase_cons_head]
  · rintro ⟨x, l'⟩ hp
    simp only [Finset.mem_sigma, Multiset.mem_toFinset, mem_ordL] at hp
    show l' ++ [x] ∈ ordL m
    rw [mem_ordL, ← Multiset.coe_add, hp.2, add_comm]
    simpa using Multiset.cons_erase hp.1
  · intro l hl
    rw [mem_ordL] at hl
    have hne : l ≠ [] := by rintro rfl; simp at hl; exact hm hl.symm
    have hlast : l.getLastD 0 = l.getLast hne := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
    simp only [hlast]
    exact List.dropLast_append_getLast hne
  · rintro ⟨x, l'⟩ hp
    simp
  · intro l hl
    rw [mem_ordL] at hl
    have hne : l ≠ [] := by rintro rfl; simp at hl; exact hm hl.symm
    have hlast : l.getLastD 0 = l.getLast hne := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
    simp only [hlast]
    rw [List.dropLast_append_getLast hne]

/-- The sum over the orderings of a multiset `m` of positive integers of the reciprocal of the
product of the partial sums: `∑_l 1/Dp 1 l = 1/(∏ m · ∏_j c_j!)`. -/
theorem orderingSum (n : ℕ) : ∀ m : Multiset ℕ, Multiset.card m = n → (∀ x ∈ m, 0 < x) →
    ∑ l ∈ ordL m, (1 : ℝ) / (Dp 1 l : ℝ) = 1 / ((m.prod : ℝ) * (cfact m : ℝ)) := by
  induction n with
  | zero =>
    intro m hc _
    have hm : m = 0 := Multiset.card_eq_zero.mp hc
    subst hm
    have : ordL 0 = {[]} := by
      ext l
      simp [mem_ordL, Multiset.coe_eq_zero]
    simp [this, Dp, cfact]
  | succ n ih =>
    intro m hc hpos
    have hm0 : m ≠ 0 := by
      intro h; subst h; simp at hc
    rw [sum_ordL m hm0]
    have hS : 0 < m.sum := by
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hm0
      exact lt_of_lt_of_le (hpos x hx) (Multiset.le_sum_of_mem hx)
    have hSR : (0 : ℝ) < (m.sum : ℝ) := by exact_mod_cast hS
    have inner : ∀ x ∈ m.toFinset,
        ∑ l ∈ ordL (m.erase x), (1 : ℝ) / (Dp 1 (l ++ [x]) : ℝ) =
          (x * m.count x : ℝ) / ((m.sum : ℝ) * ((m.prod : ℝ) * (cfact m : ℝ))) := by
      intro x hx
      rw [Multiset.mem_toFinset] at hx
      have hcard : Multiset.card (m.erase x) = n := by
        rw [Multiset.card_erase_of_mem hx, hc]; rfl
      have hpos' : ∀ y ∈ m.erase x, 0 < y := fun y hy => hpos y (Multiset.mem_of_mem_erase hy)
      have h1 := ih (m.erase x) hcard hpos'
      have hsum : ∀ l ∈ ordL (m.erase x), Dp 1 (l ++ [x]) = Dp 1 l * m.sum := by
        intro l hl
        rw [mem_ordL] at hl
        rw [Dp_append]
        congr 1
        have h2 : l.sum = (m.erase x).sum := by rw [← hl]; simp
        have h3 := Multiset.sum_erase hx
        omega
      rw [Finset.sum_congr rfl (fun l hl => by rw [hsum l hl])]
      simp only [Nat.cast_mul]
      have : ∀ l ∈ ordL (m.erase x), (1 : ℝ) / ((Dp 1 l : ℝ) * (m.sum : ℝ)) =
          (1 / (m.sum : ℝ)) * ((1 : ℝ) / (Dp 1 l : ℝ)) := by
        intro l _; field_simp
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, h1]
      have hP := Multiset.prod_erase hx
      have hC := cfact_erase hx
      have hxpos : (0 : ℝ) < x := by exact_mod_cast hpos x hx
      have hcnt : (0 : ℝ) < m.count x := by exact_mod_cast Multiset.count_pos.mpr hx
      have hPe : (0 : ℝ) < ((m.erase x).prod : ℕ) := by
        exact_mod_cast Multiset.prod_pos hpos'
      have hCe : (0 : ℝ) < (cfact (m.erase x) : ℕ) := by
        have : cfact m ≠ 0 := by
          unfold cfact
          exact Finset.prod_ne_zero_iff.mpr (fun j _ => (Nat.factorial_pos _).ne')
        have h4 : cfact (m.erase x) ≠ 0 := by
          intro h; apply this; rw [hC, h]; simp
        exact_mod_cast Nat.pos_of_ne_zero h4
      have hPR : (m.prod : ℝ) = x * ((m.erase x).prod : ℕ) := by
        rw [← hP]; push_cast; ring
      have hCR : (cfact m : ℝ) = (cfact (m.erase x) : ℕ) * m.count x := by
        rw [hC]; push_cast; ring
      rw [hPR, hCR]
      field_simp
    rw [Finset.sum_congr rfl inner, ← Finset.sum_div]
    have hsumx : ∑ x ∈ m.toFinset, ((x : ℝ) * (m.count x : ℝ)) = (m.sum : ℝ) := by
      have := Finset.sum_multiset_count m
      have h5 : (m.sum : ℝ) = ((∑ x ∈ m.toFinset, m.count x • x : ℕ) : ℝ) := by rw [← this]
      rw [h5]
      push_cast
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp [mul_comm]
    rw [hsumx]
    field_simp

/-! ## The Ewens formula and the spacing law -/

/-- The Ewens sampling formula, `T!/α^{(T)} ∏_{j=1}^{T} (α/j)^{c_j}/c_j!`, where `c_j` is the number
of parts of `m` equal to `j`. -/
noncomputable def esf (α : ℝ) (T : ℕ) (m : Multiset ℕ) : ℝ :=
  (T.factorial : ℝ) / rpoch α T *
    ∏ j ∈ Icc 1 T, (α / j) ^ (m.count j) / ((m.count j).factorial : ℝ)

/-- The Ewens formula in terms of the number of parts, the product of the parts and the product
of the factorials of the multiplicities. -/
theorem esf_compact {α : ℝ} (hα : 0 < α) {T : ℕ} {m : Multiset ℕ} (hpos : ∀ x ∈ m, 0 < x)
    (hsum : m.sum = T) :
    esf α T m = (T.factorial : ℝ) / rpoch α T * (α ^ Multiset.card m / ((m.prod : ℝ) * (cfact m : ℝ))) := by
  unfold esf
  congr 1
  have hsub : m.toFinset ⊆ Icc 1 T := by
    intro x hx
    rw [Multiset.mem_toFinset] at hx
    simp only [mem_Icc]
    exact ⟨hpos x hx, hsum ▸ Multiset.le_sum_of_mem hx⟩
  rw [← Finset.prod_subset hsub (fun j _ hj => by
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hj
    simp [hj])]
  rw [Finset.prod_div_distrib]
  have hp : (m.prod : ℝ) = ∏ j ∈ m.toFinset, (j : ℝ) ^ m.count j := by
    have := Finset.prod_multiset_count m
    exact_mod_cast this
  have hc : (cfact m : ℝ) = ∏ j ∈ m.toFinset, ((m.count j).factorial : ℝ) := by
    unfold cfact; push_cast; rfl
  simp only [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Multiset.toFinset_sum_count_eq, hp, hc]
  field_simp

theorem Dp_pos : ∀ (l : List ℕ), (∀ x ∈ l, 0 < x) → ∀ s : ℕ, 1 ≤ s → 0 < Dp s l := by
  intro l
  induction l with
  | nil => intro _ s _; simp [Dp]
  | cons x r ih =>
    intro hl s hs
    have hx : 0 < x := hl x (by simp)
    simp only [Dp]
    exact Nat.mul_pos (by omega) (ih (fun y hy => hl y (by simp [hy])) (s + x) (by omega))

/-- The law of the multiset of the spacings of `T` independent trials with success probabilities
`fT α t`: the sum over the distinct orderings `l` of `m` (the runs, in order) of the probability
`runProb α 1 l` of the runs. -/
noncomputable def spLaw (α : ℝ) (m : Multiset ℕ) : ℝ := ∑ l ∈ ordL m, runProb α 1 l

/-- The spacing side of `rem:aging-feller`: the law of the multiset of spacings is the Ewens
formula. -/
theorem spLaw_eq_esf {α : ℝ} (hα : 0 < α) {T : ℕ} {m : Multiset ℕ} (hpos : ∀ x ∈ m, 0 < x)
    (hsum : m.sum = T) : spLaw α m = esf α T m := by
  rw [esf_compact hα hpos hsum]
  have hrp : 0 < rpoch α T := rpoch_pos hα T
  have hcard : ∀ l ∈ ordL m, runProb α 1 l = α ^ Multiset.card m * (T.factorial : ℝ) / (rpoch α T * (Dp 1 l : ℝ)) := by
    intro l hl
    rw [mem_ordL] at hl
    have hlpos : ∀ x ∈ l, 0 < x := fun x hx => hpos x (by rw [← hl]; simpa using hx)
    have hlsum : l.sum = T := by rw [← hsum, ← hl]; simp
    have hlen : l.length = Multiset.card m := by rw [← hl]; simp
    have h := runProb_closed hα l hlpos 1 le_rfl
    rw [hlsum, hlen] at h
    simp only [Nat.cast_one, add_sub_cancel_right, Nat.sub_self, Nat.factorial_zero, Nat.cast_one,
      mul_one, Nat.add_sub_cancel_left] at h
    have hD : (0 : ℝ) < (Dp 1 l : ℝ) := by exact_mod_cast Dp_pos l hlpos 1 le_rfl
    rw [eq_div_iff (by positivity)]
    rw [← h]
  unfold spLaw
  rw [Finset.sum_congr rfl hcard]
  have hord := orderingSum (Multiset.card m) m rfl hpos
  have : ∑ l ∈ ordL m, α ^ Multiset.card m * (T.factorial : ℝ) / (rpoch α T * (Dp 1 l : ℝ)) =
      (α ^ Multiset.card m * (T.factorial : ℝ) / rpoch α T) * ∑ l ∈ ordL m, (1 : ℝ) / (Dp 1 l : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    field_simp
  rw [this, hord]
  field_simp

/-! ## The restaurant side -/

/-- The law of the multiset of the table sizes of the Chinese restaurant process with parameter
`α` after `T` customers, as a forward equation over the predecessors. Customer `T+1` opens a new
table with probability `α/(α+T)` and joins one given table of size `n` with probability
`n/(α+T)`. A multiset `m` of `T+1` customers is reached from `m.erase 1` by a new table, and,
for each size `x ≥ 2` present in `m`, from `(x-1) ::ₘ m.erase x` by growing one of the tables of
size `x - 1` there (`(m.erase x).count (x-1) + 1` of them, each with probability `(x-1)/(α+T)`).
The definition is meant for multisets of positive integers whose sum is `T`. -/
noncomputable def crpLaw (α : ℝ) : ℕ → Multiset ℕ → ℝ
  | 0, m => if m = 0 then 1 else 0
  | T + 1, m => ∑ x ∈ m.toFinset,
      if x = 1 then α / (α + T) * crpLaw α T (m.erase 1)
      else (((m.erase x).count (x - 1) + 1 : ℕ) * ((x - 1 : ℕ) : ℝ)) / (α + T) *
        crpLaw α T ((x - 1) ::ₘ m.erase x)

/-- The Ewens formula in the compact form of `esf_compact`. -/
noncomputable def esfC (α : ℝ) (T : ℕ) (m : Multiset ℕ) : ℝ :=
  (T.factorial : ℝ) / rpoch α T * (α ^ Multiset.card m / ((m.prod : ℝ) * (cfact m : ℝ)))

theorem crp_term {α : ℝ} (hα : 0 < α) (T : ℕ)
    (ih : ∀ p : Multiset ℕ, (∀ x ∈ p, 0 < x) → p.sum = T → crpLaw α T p = esfC α T p)
    {m : Multiset ℕ} (hpos : ∀ x ∈ m, 0 < x) (hsum : m.sum = T + 1) {x : ℕ} (hx : x ∈ m) :
    (if x = 1 then α / (α + T) * crpLaw α T (m.erase 1)
      else (((m.erase x).count (x - 1) + 1 : ℕ) * ((x - 1 : ℕ) : ℝ)) / (α + T) *
        crpLaw α T ((x - 1) ::ₘ m.erase x)) =
      esfC α (T + 1) m * ((x : ℝ) * (m.count x : ℝ)) / ((T : ℝ) + 1) := by
  have hxpos : 0 < x := hpos x hx
  set n := m.erase x with hn
  have hnpos : ∀ y ∈ n, 0 < y := fun y hy => hpos y (Multiset.mem_of_mem_erase hy)
  have hP : (m.prod : ℝ) = x * (n.prod : ℝ) := by
    rw [← Multiset.prod_erase hx]; push_cast; rfl
  have hC : (cfact m : ℝ) = (cfact n : ℝ) * (m.count x : ℝ) := by
    rw [cfact_erase hx]; push_cast; rfl
  have hcard : Multiset.card m = Multiset.card n + 1 := by
    rw [hn, Multiset.card_erase_of_mem hx, Nat.pred_eq_sub_one]
    have : 0 < Multiset.card m := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx⟩
    omega
  have hnsum : n.sum + x = T + 1 := by
    rw [← hsum, hn]; have := Multiset.sum_erase hx; omega
  have hPn : (0 : ℝ) < (n.prod : ℝ) := by exact_mod_cast Multiset.prod_pos hnpos
  have hCn : (0 : ℝ) < (cfact n : ℝ) := by
    have : cfact n ≠ 0 := by
      unfold cfact
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => (Nat.factorial_pos _).ne')
    exact_mod_cast Nat.pos_of_ne_zero this
  have hcnt : (0 : ℝ) < (m.count x : ℝ) := by exact_mod_cast Multiset.count_pos.mpr hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hρ : 0 < rpoch α T := rpoch_pos hα T
  have hαT : 0 < α + T := by positivity
  have hρs : rpoch α (T + 1) = rpoch α T * (α + T) := rpoch_succ α T
  have hfac : ((T + 1).factorial : ℝ) = ((T : ℝ) + 1) * (T.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  unfold esfC
  rw [hρs, hfac, hP, hC, hcard]
  by_cases h1 : x = 1
  · subst h1
    simp only [if_true]
    have hn' : n.sum = T := by omega
    rw [ih n hnpos hn']
    unfold esfC
    push_cast
    field_simp
    ring
  · simp only [h1, if_false]
    have hx2 : 2 ≤ x := by omega
    have hp_pos : ∀ y ∈ (x - 1) ::ₘ n, 0 < y := by
      intro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · omega
      · exact hnpos y hy
    have hp_sum : ((x - 1) ::ₘ n).sum = T := by
      rw [Multiset.sum_cons]; omega
    rw [ih _ hp_pos hp_sum]
    unfold esfC
    have hPp : (((x - 1) ::ₘ n).prod : ℝ) = ((x - 1 : ℕ) : ℝ) * (n.prod : ℝ) := by
      rw [Multiset.prod_cons]; push_cast; rfl
    have hCp : (cfact ((x - 1) ::ₘ n) : ℝ) = (cfact n : ℝ) * ((n.count (x - 1) + 1 : ℕ) : ℝ) := by
      rw [cfact_cons]; push_cast; rfl
    have hcardp : Multiset.card ((x - 1) ::ₘ n) = Multiset.card n + 1 := Multiset.card_cons _ _
    have hx1 : (0 : ℝ) < ((x - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < x - 1)
    have hcc : (0 : ℝ) < ((n.count (x - 1) + 1 : ℕ) : ℝ) := by positivity
    rw [hPp, hCp, hcardp]
    field_simp

theorem crpLaw_eq_esfC {α : ℝ} (hα : 0 < α) (T : ℕ) :
    ∀ m : Multiset ℕ, (∀ x ∈ m, 0 < x) → m.sum = T → crpLaw α T m = esfC α T m := by
  induction T with
  | zero =>
    intro m hpos hsum
    have hm : m = 0 := by
      by_contra hne
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      have := Multiset.le_sum_of_mem hx
      have := hpos x hx
      omega
    subst hm
    simp [crpLaw, esfC, cfact, rpoch]
  | succ T ih =>
    intro m hpos hsum
    rw [crpLaw]
    rw [Finset.sum_congr rfl (fun x hx => crp_term hα T ih hpos hsum (Multiset.mem_toFinset.mp hx))]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have hsumx : ∑ x ∈ m.toFinset, ((x : ℝ) * (m.count x : ℝ)) = (T : ℝ) + 1 := by
      have := Finset.sum_multiset_count m
      have h5 : ((T + 1 : ℕ) : ℝ) = ((∑ x ∈ m.toFinset, m.count x • x : ℕ) : ℝ) := by
        rw [← this, hsum]
      push_cast at h5
      rw [h5]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp [mul_comm]
    rw [hsumx]
    have : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    field_simp

/-- The restaurant side of `rem:aging-feller`: the law of the multiset of table sizes is the Ewens
formula. -/
theorem crpLaw_eq_esf {α : ℝ} (hα : 0 < α) {T : ℕ} {m : Multiset ℕ} (hpos : ∀ x ∈ m, 0 < x)
    (hsum : m.sum = T) : crpLaw α T m = esf α T m := by
  rw [esf_compact hα hpos hsum]
  exact crpLaw_eq_esfC hα T m hpos hsum

/-- `rem:aging-feller`, the Feller coupling for a fixed number `T` of trials or customers: the
multiset of the spacings between the successes of independent trials with success probabilities
`f_t = α/(α+t-1)` (`spLaw`, with `α = dθ`) has the same law as the multiset of the table sizes of
the Chinese restaurant process with parameter `α` (`crpLaw`), for every multiset `m` of positive
integers with sum `T`. -/
theorem feller_coupling {α : ℝ} (hα : 0 < α) {T : ℕ} {m : Multiset ℕ} (hpos : ∀ x ∈ m, 0 < x)
    (hsum : m.sum = T) : spLaw α m = crpLaw α T m := by
  rw [spLaw_eq_esf hα hpos hsum, crpLaw_eq_esf hα hpos hsum]

/-- `rem:aging-feller`: for `α = dθ` and a fixed number `T` of trials or customers, the multiset
of the spacings between the successes of the independent trials with success probabilities
`f_t = dθ/(dθ+t-1)` has the same law as the multiset of the table sizes of the Chinese restaurant
process with parameter `dθ` (the Feller coupling). This is `feller_coupling`. -/
theorem rem_aging_feller {α : ℝ} (hα : 0 < α) {T : ℕ} {m : Multiset ℕ} (hpos : ∀ x ∈ m, 0 < x)
    (hsum : m.sum = T) : spLaw α m = crpLaw α T m := feller_coupling hα hpos hsum

end Kagey131.PaperD.S4
