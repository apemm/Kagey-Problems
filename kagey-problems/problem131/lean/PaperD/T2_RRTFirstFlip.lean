import PaperD.T2_RRTFirstD
import PaperD.T2_RRTForced

/-!
# Paper D, Lemma 3.3 (`lem:firstmark`): the decomposition of `f_N(m)` at the first flip

Let `V = j` be the first marked vertex (Lean index `a = j - 1`, `1 ≤ a ≤ t`, `N = t + 1`), and
`S = 𝒯_V` its family, `|S| = d`. The paper's proof of Lemma 3.3 shows that, given `V = j` and
`|S| = d`, the number of vertices of `S` that are *even* (they flip back; this is `Y_d`) and the
number of odd vertices outside `S` (this is `Z^{(j)}_{N-d}`) are independent, with the laws of
`M^{[1]}_d` and `M^{[j-1]}_{N-d}`. Here:

* `evenIn T μ a`, `oddOut T μ a`: the two counts; `oddCount_eq_of_firstAt`: on `V = a`,
  `M_N = (d - evenIn) + oddOut`.
* `rrt_firstFlip_joint`: the joint law
  `P(V = j, |S| = d, evenIn = y, oddOut = z) = ε(1-ε)^{j-2} β_j(d) P(Y_d = y) P(Z^{(j)}_{N-d} = z)`
  for all `d, y, z`, with `β_j = stLaw j (N - j)`, `P(Y_d = y) = law ε d y` and
  `P(Z^{(j)}_{N-d} = z) = lawFrom ε (j-1) (N - d - (j-1)) z`.
* `rrt_fN_decomp`: **the formula of Lemma 3.3**: for `m ≥ 1`,
  `f_N(m) = ∑_{j=2}^N ε(1-ε)^{j-2} ∑_d β_j(d) P(d - Y_d + Z^{(j)}_{N-d} = m)`
  with `Y_d` and `Z^{(j)}_{N-d}` independent (`convYZ`).

**Route.** The paper conditions on the vertex set `S` and uses Lemma 3.2 (`lem:split`) to see two
independent random recursive trees. Lemma 3.2 itself is not formalized here. Instead the joint
law is proved by induction on `N`, adding one vertex at a time and using the two one-step facts of
the paper (Lemma 3.1's proof and the urn step after it): the new vertex joins `S` with probability
`d/N'` (`N'` the current size), and given that, it is even/odd in `S`, resp. odd/even outside `S`,
with the up-probabilities `r_d(y)` resp. `r_{N'-d}(z)`. The product form
`β · P(Y = y) · P(Z = z)` is shown to satisfy the resulting forward equation (`RS_succ`), via one
generic summation identity for up-or-stay chains (`dual_sum`).
-/

namespace Kagey131.PaperD
namespace RRT

open Finset

/-! ### The two counts -/

/-- The number of *even* vertices in the family of `a` (vertices of `𝒯_a` with an even number of
marks on their path to the root). -/
noncomputable def evenIn {t : ℕ} (T : IncTree t) (μ : Word t) (a : ℕ) : ℕ :=
  (univ.filter (fun u : Fin (t + 1) => (∃ w ∈ anc T u, (w : ℕ) = a) ∧ flips T μ u % 2 = 0)).card

/-- The number of *odd* vertices outside the family of `a`. -/
noncomputable def oddOut {t : ℕ} (T : IncTree t) (μ : Word t) (a : ℕ) : ℕ :=
  (univ.filter (fun u : Fin (t + 1) => ¬ (∃ w ∈ anc T u, (w : ℕ) = a) ∧ flips T μ u % 2 = 1)).card

theorem inFam_snoc_castSucc {t a : ℕ} (T : IncTree t) (p : Fin (t + 1)) (i : Fin (t + 1)) :
    (∃ w ∈ anc (T.snoc p) i.castSucc, (w : ℕ) = a) ↔ (∃ w ∈ anc T i, (w : ℕ) = a) := by
  rw [anc_snoc_castSucc]
  simp

theorem inFam_snoc_last {t a : ℕ} (ha : a ≤ t) (T : IncTree t) (p : Fin (t + 1)) :
    (∃ w ∈ anc (T.snoc p) (Fin.last (t + 1)), (w : ℕ) = a) ↔ (∃ w ∈ anc T p, (w : ℕ) = a) := by
  rw [anc_snoc_last]
  have : t + 1 ≠ a := by omega
  simp [this]

theorem evenIn_snoc {t a : ℕ} (ha : a ≤ t) (T : IncTree t) (p : Fin (t + 1)) (μ : Word t)
    (m : Bool) :
    evenIn (T.snoc p) (Fin.snoc μ m : Word (t + 1)) a = evenIn T μ a +
      if (∃ w ∈ anc T p, (w : ℕ) = a) ∧ (flips T μ p + if m = true then 1 else 0) % 2 = 0
      then 1 else 0 := by
  unfold evenIn
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [inFam_snoc_castSucc, flips_snoc_castSucc]
  · simp only [inFam_snoc_last ha, flips_snoc_last]

theorem oddOut_snoc {t a : ℕ} (ha : a ≤ t) (T : IncTree t) (p : Fin (t + 1)) (μ : Word t)
    (m : Bool) :
    oddOut (T.snoc p) (Fin.snoc μ m : Word (t + 1)) a = oddOut T μ a +
      if ¬ (∃ w ∈ anc T p, (w : ℕ) = a) ∧ (flips T μ p + if m = true then 1 else 0) % 2 = 1
      then 1 else 0 := by
  unfold oddOut
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [inFam_snoc_castSucc, flips_snoc_castSucc]
  · simp only [inFam_snoc_last ha, flips_snoc_last]

/-! ### Facts under `V = a` -/

/-- Below the first marked vertex every vertex is even: its whole path is unmarked. -/
theorem flips_eq_zero_of_lt {t a : ℕ} {T : IncTree t} {μ : Word t} (hf : firstAt μ a)
    {u : Fin (t + 1)} (hu : (u : ℕ) < a) : flips T μ u = 0 := by
  unfold flips
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw
  have := le_of_mem_anc hw
  rw [hf.1 w (by omega)]
  simp

/-- The root is not in the family of `a ≥ 1`. -/
theorem not_inFam_zero {t a : ℕ} (ha : 1 ≤ a) (T : IncTree t) :
    ¬ (∃ w ∈ anc T 0, (w : ℕ) = a) := by
  rintro ⟨w, hw, hwa⟩
  have h := le_of_mem_anc hw
  rw [Fin.val_zero] at h
  omega

/-- The family of `a ≥ 1` misses the root, so it has at most `t` vertices. -/
theorem subtreeSize_le {t a : ℕ} (ha : 1 ≤ a) (T : IncTree t) : subtreeSize T a ≤ t := by
  unfold subtreeSize
  have h : (univ.filter (fun u : Fin (t + 1) => ∃ w ∈ anc T u, (w : ℕ) = a)) ⊆ univ.erase 0 := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    exact not_inFam_zero ha T hu.2
  have := Finset.card_le_card h
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  omega

/-! ### The tree side as a functional -/

/-- `E[g(|𝒯_a|, evenIn, oddOut); V = a]` in the tree model with `Bernoulli(ε)` marks. -/
noncomputable def TS (ε : ℝ) (a t : ℕ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ _s : Bool, ∑ T : IncTree t, ∑ μ : Word t,
    (if firstAt μ a then weight (fun _ => ε) t T μ else 0) *
      g (subtreeSize T a) (evenIn T μ a) (oddOut T μ a)

/-- One step of the joint chain `(|S|, evenIn, oddOut)` at size `t+1`, as an operator on test
functions: the new vertex joins `S` with probability `d/(t+1)`, then it is even with probability
`r_d(y)`; otherwise it is odd with probability `r_{t+1-d}(z)`. -/
noncomputable def Kop (ε : ℝ) (t : ℕ) (g : ℕ → ℕ → ℕ → ℝ) (d y z : ℕ) : ℝ :=
  1 / ((t : ℝ) + 1) *
    ((d : ℝ) * (upProb ε d y * g (d + 1) (y + 1) z + (1 - upProb ε d y) * g (d + 1) y z) +
      ((t + 1 - d : ℕ) : ℝ) *
        (upProb ε (t + 1 - d) z * g d y (z + 1) + (1 - upProb ε (t + 1 - d) z) * g d y z))

/-- The one-vertex step on a fixed configuration with `V = a`. -/
theorem key_step (ε : ℝ) {t a : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) (T : IncTree t) (μ : Word t)
    (g : ℕ → ℕ → ℕ → ℝ) :
    ∑ p : Fin (t + 1), ∑ m : Bool, 1 / ((t : ℝ) + 1) * markW ε m *
        g (subtreeSize (T.snoc p) a) (evenIn (T.snoc p) (Fin.snoc μ m : Word (t + 1)) a)
          (oddOut (T.snoc p) (Fin.snoc μ m : Word (t + 1)) a) =
      Kop ε t g (subtreeSize T a) (evenIn T μ a) (oddOut T μ a) := by
  set d := subtreeSize T a with hd
  set y := evenIn T μ a with hy
  set z := oddOut T μ a with hz
  -- the four values reached
  set X1 := (1 - ε) * g (d + 1) (y + 1) z + ε * g (d + 1) y z
  set X2 := (1 - ε) * g (d + 1) y z + ε * g (d + 1) (y + 1) z
  set X3 := (1 - ε) * g d y (z + 1) + ε * g d y z
  set X4 := (1 - ε) * g d y z + ε * g d y (z + 1)
  have hp : ∀ p : Fin (t + 1), ∑ m : Bool, 1 / ((t : ℝ) + 1) * markW ε m *
        g (subtreeSize (T.snoc p) a) (evenIn (T.snoc p) (Fin.snoc μ m : Word (t + 1)) a)
          (oddOut (T.snoc p) (Fin.snoc μ m : Word (t + 1)) a) =
      1 / ((t : ℝ) + 1) *
        ((if (∃ w ∈ anc T p, (w : ℕ) = a) ∧ flips T μ p % 2 = 0 then 1 else 0) * (X1 - X2) +
          (if (∃ w ∈ anc T p, (w : ℕ) = a) then 1 else 0) * X2 +
          (if ¬ (∃ w ∈ anc T p, (w : ℕ) = a) ∧ flips T μ p % 2 = 1 then 1 else 0) * (X3 - X4) +
          (1 - (if (∃ w ∈ anc T p, (w : ℕ) = a) then 1 else 0)) * X4) := by
    intro p
    rw [Fintype.sum_bool]
    simp only [subtreeSize_snoc hat, evenIn_snoc hat, oddOut_snoc hat, markW, if_true,
      Bool.false_eq_true, if_false, add_zero]
    by_cases hin : ∃ w ∈ anc T p, (w : ℕ) = a
    · rcases Nat.mod_two_eq_zero_or_one (flips T μ p) with h | h
      · have h' : (flips T μ p + 1) % 2 = 1 := by omega
        simp only [hin, h, h', true_and, not_true_eq_false, false_and, if_true, if_false,
          add_zero, ← hd, ← hy, ← hz]
        norm_num
        ring
      · have h' : (flips T μ p + 1) % 2 = 0 := by omega
        simp only [hin, h, h', true_and, not_true_eq_false, false_and, if_true, if_false,
          add_zero, ← hd, ← hy, ← hz]
        norm_num
        ring
    · rcases Nat.mod_two_eq_zero_or_one (flips T μ p) with h | h
      · have h' : (flips T μ p + 1) % 2 = 1 := by omega
        simp only [hin, h, h', true_and, not_false_eq_true, false_and, if_true, if_false,
          add_zero, ← hd, ← hy, ← hz]
        norm_num
        ring
      · have h' : (flips T μ p + 1) % 2 = 0 := by omega
        simp only [hin, h, h', true_and, not_false_eq_true, false_and, if_true, if_false,
          add_zero, ← hd, ← hy, ← hz]
        norm_num
        ring
  rw [Finset.sum_congr rfl (fun p _ => hp p), ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have c1 : (∑ p : Fin (t + 1), if (∃ w ∈ anc T p, (w : ℕ) = a) ∧ flips T μ p % 2 = 0
      then (1 : ℝ) else 0) = y := by
    rw [hy]; unfold evenIn; rw [Finset.card_filter]; push_cast; rfl
  have c2 : (∑ p : Fin (t + 1), if (∃ w ∈ anc T p, (w : ℕ) = a) then (1 : ℝ) else 0) = d :=
    count_join T a
  have c3 : (∑ p : Fin (t + 1), if ¬ (∃ w ∈ anc T p, (w : ℕ) = a) ∧ flips T μ p % 2 = 1
      then (1 : ℝ) else 0) = z := by
    rw [hz]; unfold oddOut; rw [Finset.card_filter]; push_cast; rfl
  rw [c1, c2, c3]
  -- now the algebra
  have hd1 : 1 ≤ d := subtreeSize_pos T hat
  have hdt : d ≤ t := subtreeSize_le ha1 T
  unfold Kop
  have hn : ((t + 1 - d : ℕ) : ℝ) = (t : ℝ) + 1 - d := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hn]
  have hd0 : (d : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
                               linarith
  have hn0 : (((t + 1 - d : ℕ) : ℝ)) ≠ 0 := by
    have : 1 ≤ t + 1 - d := by omega
    have : (1 : ℝ) ≤ ((t + 1 - d : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  rw [hn] at hn0
  unfold upProb
  have hcast : (((t + 1 - d : ℕ) : ℕ) : ℝ) = (t : ℝ) + 1 - d := hn
  rw [hcast]
  simp only [X1, X2, X3, X4]
  field_simp
  push_cast
  ring

/-- The tree side moves by `Kop`. -/
theorem TS_succ (ε : ℝ) {a t : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) (g : ℕ → ℕ → ℕ → ℝ) :
    TS ε a (t + 1) g = TS ε a t (Kop ε t g) := by
  unfold TS
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sum_tree_succ]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.sum_congr rfl (fun p _ => sum_word_snoc _), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  by_cases hf : firstAt μ a
  · rw [if_pos hf, ← key_step ε ha1 hat T μ g, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [if_pos ((firstAt_snoc_old hat μ m).2 hf), weight_snoc]
    ring
  · rw [if_neg hf, zero_mul]
    refine Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun m _ => ?_))
    rw [if_neg (fun h => hf ((firstAt_snoc_old hat μ m).1 h)), zero_mul]

/-- At the time `t = a` when the first marked vertex `a` arrives: `S = {a}`, `a` is odd and all
other vertices are even. -/
theorem TS_base (ε : ℝ) {a : ℕ} (ha1 : 1 ≤ a) (g : ℕ → ℕ → ℕ → ℝ) :
    TS ε a a g = ε * (1 - ε) ^ (a - 1) * g 1 0 0 := by
  have hstat : ∀ (T : IncTree a) (μ : Word a), firstAt μ a →
      subtreeSize T a = 1 ∧ evenIn T μ a = 0 ∧ oddOut T μ a = 0 := by
    intro T μ hf
    refine ⟨subtreeSize_top T, ?_, ?_⟩
    · unfold evenIn
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro u - ⟨⟨w, hw, hwa⟩, hev⟩
      have h1 := le_of_mem_anc hw
      have hu : u = Fin.last a := Fin.ext (by have := u.isLt; simp; omega)
      subst hu
      -- the flips of `a` are `1`: only `a` itself is marked on its path
      have : flips T μ (Fin.last a) = 1 := by
        unfold flips
        rw [Finset.card_eq_one]
        refine ⟨Fin.last a, ?_⟩
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hm⟩
          have := le_of_mem_anc hx
          by_contra hne
          have hlt : (x : ℕ) < a := by
            have : (x : ℕ) ≠ a := fun h => hne (Fin.ext (by simpa using h))
            simp at this ⊢; omega
          rw [hf.1 x hlt] at hm
          exact Bool.false_ne_true hm
        · rintro rfl
          refine ⟨self_mem_anc T _, ?_⟩
          obtain ⟨u, hu, hm⟩ := hf.2
          have : u = Fin.last a := Fin.ext (by simpa using hu)
          rw [← this]; exact hm
      rw [this] at hev
      omega
    · unfold oddOut
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro u - ⟨hnot, hodd⟩
      have hlt : (u : ℕ) < a := by
        by_contra hge
        have hu : u = Fin.last a := Fin.ext (by have := u.isLt; simp; omega)
        exact hnot ⟨u, self_mem_anc T u, by rw [hu]; simp⟩
      rw [flips_eq_zero_of_lt hf hlt] at hodd
      omega
  have h1 : TS ε a a g = rrtProb (fun _ => ε) a (fun _ _ μ => True ∧ firstAt μ a) * g 1 0 0 := by
    unfold TS rrtProb
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    by_cases hf : firstAt μ a
    · obtain ⟨e1, e2, e3⟩ := hstat T μ hf
      rw [if_pos hf, if_pos ⟨trivial, hf⟩, e1, e2, e3]
    · rw [if_neg hf, if_neg (fun h => hf h.2), zero_mul, zero_mul]
  rw [h1, rrtProb_and, treeProb_true, one_mul, markProb_firstAt _ ha1 le_rfl]
  simp only [Finset.prod_const, Finset.card_range]
  ring

/-! ### The product side -/

/-- One summation identity for an up-or-stay chain: if `Q(0) = P(0)(1 - r(0))` and
`Q(b+1) = P(b+1)(1 - r(b+1)) + P(b) r(b)`, and `P(R) = 0`, then
`∑_{b ≤ R} Q(b) h(b) = ∑_{b < R} P(b) (r(b) h(b+1) + (1 - r(b)) h(b))`. -/
theorem dual_sum (P Q r h : ℕ → ℝ) (R : ℕ) (h0 : Q 0 = P 0 * (1 - r 0))
    (hs : ∀ b, Q (b + 1) = P (b + 1) * (1 - r (b + 1)) + P b * r b) (hR : P R = 0) :
    ∑ b ∈ range (R + 1), Q b * h b = ∑ b ∈ range R, P b * (r b * h (b + 1) + (1 - r b) * h b) := by
  rw [Finset.sum_range_succ']
  simp only [hs, h0, add_mul, Finset.sum_add_distrib]
  have e1 : ∑ b ∈ range R, P (b + 1) * (1 - r (b + 1)) * h (b + 1) + P 0 * (1 - r 0) * h 0 =
      ∑ b ∈ range R, P b * (1 - r b) * h b := by
    rw [← Finset.sum_range_succ' (fun b => P b * (1 - r b) * h b), Finset.sum_range_succ, hR]
    ring
  have e2 : ∑ b ∈ range R, P b * (r b * h (b + 1) + (1 - r b) * h b) =
      ∑ b ∈ range R, P b * r b * h (b + 1) + ∑ b ∈ range R, P b * (1 - r b) * h b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [e2, ← e1]
  ring

theorem lawFrom_eq_zero (ε : ℝ) (k₀ : ℕ) : ∀ {m z : ℕ}, m < z → lawFrom ε k₀ m z = 0
  | 0, z, h => by simp [lawFrom]; omega
  | m + 1, z, h => by
    obtain ⟨b, rfl⟩ : ∃ b, z = b + 1 := ⟨z - 1, by omega⟩
    simp only [lawFrom]
    rw [lawFrom_eq_zero ε k₀ (by omega), lawFrom_eq_zero ε k₀ (by omega)]
    ring

/-- `∑_{y,z} P(Y_d = y) P(Z = z) g(d, y, z)` at size `t+1`, `Z` the chain `M^{[a]}` at time
`t + 1 - d`. -/
noncomputable def Inner (ε : ℝ) (a t d : ℕ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ y ∈ range (t + 2), ∑ z ∈ range (t + 2), law ε d y * lawFrom ε a (t + 1 - d - a) z * g d y z

/-- The product side: `ε(1-ε)^{a-1} ∑_d β(d) ∑_{y,z} P(Y_d = y) P(Z = z) g(d, y, z)`. -/
noncomputable def RS (ε : ℝ) (a t : ℕ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ε * (1 - ε) ^ (a - 1) * ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * Inner ε a t d g

theorem RS_base (ε : ℝ) (a : ℕ) (g : ℕ → ℕ → ℕ → ℝ) :
    RS ε a a g = ε * (1 - ε) ^ (a - 1) * g 1 0 0 := by
  unfold RS
  congr 1
  rw [Finset.sum_eq_single_of_mem 1 (by simp) (fun d _ hd => by
    rw [Nat.sub_self]; simp [stLaw, hd])]
  rw [Nat.sub_self]
  simp only [stLaw, if_true, one_mul]
  unfold Inner
  rw [Finset.sum_eq_single_of_mem 0 (by simp) (fun y _ hy => by
    simp [law_one, hy])]
  rw [Finset.sum_eq_single_of_mem 0 (by simp) (fun z _ hz => by
    rw [show a + 1 - 1 - a = 0 by omega]; simp [lawFrom, hz])]
  rw [show a + 1 - 1 - a = 0 by omega]
  simp [law_one, lawFrom]

/-- The joining part of the step: the chain `Y` moves from size `d` to size `d+1`. -/
theorem join_part (ε : ℝ) {a t d m : ℕ} (hd1 : 1 ≤ d) (hdt : d ≤ t + 1) (hm : m ≤ t + 1)
    (g : ℕ → ℕ → ℕ → ℝ) :
    (∑ y ∈ range (t + 2), ∑ z ∈ range (t + 2), lawFrom ε a m z * (law ε d y *
        (upProb ε d y * g (d + 1) (y + 1) z + (1 - upProb ε d y) * g (d + 1) y z))) =
      ∑ y ∈ range (t + 2 + 1), ∑ z ∈ range (t + 2 + 1),
        law ε (d + 1) y * lawFrom ε a m z * g (d + 1) y z := by
  rw [Finset.sum_comm]
  have h1 : ∀ z, (∑ y ∈ range (t + 2), lawFrom ε a m z * (law ε d y *
      (upProb ε d y * g (d + 1) (y + 1) z + (1 - upProb ε d y) * g (d + 1) y z))) =
      lawFrom ε a m z * ∑ y ∈ range (t + 2 + 1), law ε (d + 1) y * g (d + 1) y z := by
    intro z
    rw [← Finset.mul_sum, dual_sum (law ε d) (law ε (d + 1)) (upProb ε d)
      (fun y => g (d + 1) y z) (t + 2) (law_succ_zero ε hd1) (law_succ_succ ε hd1) ?_]
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    exact law_eq_zero ε (by omega)
  rw [Finset.sum_congr rfl (fun z _ => h1 z)]
  rw [show (∑ z ∈ range (t + 2), lawFrom ε a m z *
      ∑ y ∈ range (t + 2 + 1), law ε (d + 1) y * g (d + 1) y z) =
      ∑ z ∈ range (t + 2 + 1), lawFrom ε a m z *
      ∑ y ∈ range (t + 2 + 1), law ε (d + 1) y * g (d + 1) y z by
    rw [Finset.sum_range_succ _ (t + 2), lawFrom_eq_zero ε a (by omega), zero_mul, add_zero]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

/-- The outside part of the step: the chain `Z` moves from time `a + m` to `a + m + 1`. -/
theorem out_part (ε : ℝ) {a t d m : ℕ} (hd1 : 1 ≤ d) (hdt : d ≤ t + 1) (hm : m ≤ t + 1)
    (g : ℕ → ℕ → ℕ → ℝ) :
    (∑ y ∈ range (t + 2), ∑ z ∈ range (t + 2), law ε d y * (lawFrom ε a m z *
        (upProb ε (a + m) z * g d y (z + 1) + (1 - upProb ε (a + m) z) * g d y z))) =
      ∑ y ∈ range (t + 2 + 1), ∑ z ∈ range (t + 2 + 1),
        law ε d y * lawFrom ε a (m + 1) z * g d y z := by
  have h1 : ∀ y, (∑ z ∈ range (t + 2), law ε d y * (lawFrom ε a m z *
      (upProb ε (a + m) z * g d y (z + 1) + (1 - upProb ε (a + m) z) * g d y z))) =
      ∑ z ∈ range (t + 2 + 1), law ε d y * lawFrom ε a (m + 1) z * g d y z := by
    intro y
    rw [← Finset.mul_sum, ← dual_sum (lawFrom ε a m) (lawFrom ε a (m + 1)) (upProb ε (a + m))
      (fun z => g d y z) (t + 2) rfl (fun b => rfl) (lawFrom_eq_zero ε a (by omega)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_range_succ
    (fun y => ∑ z ∈ range (t + 2 + 1), law ε d y * lawFrom ε a (m + 1) z * g d y z) (t + 2)]
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hz : (∑ z ∈ range (t + 2 + 1), law ε (d' + 1) (t + 2) * lawFrom ε a (m + 1) z *
      g (d' + 1) (t + 2) z) = 0 := Finset.sum_eq_zero (fun z _ => by
    rw [law_eq_zero ε (show d' + 1 ≤ t + 2 by omega)]; ring)
  rw [hz, add_zero]

/-- The step for one family size `d`, multiplied by `β(d)` (zero outside the support). -/
theorem inner_step (ε : ℝ) {a t : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) (d : ℕ) (hd : d < t + 2)
    (g : ℕ → ℕ → ℕ → ℝ) :
    stLaw (a + 1) (t - a) d * Inner ε a t d (Kop ε t g) =
      stLaw (a + 1) (t - a) d * ((d : ℝ) / ((t : ℝ) + 1) * Inner ε a (t + 1) (d + 1) g +
        (1 - (d : ℝ) / ((t : ℝ) + 1)) * Inner ε a (t + 1) d g) := by
  by_cases hsupp : 1 ≤ d ∧ d ≤ t + 1 - a
  · obtain ⟨hd1, hd2⟩ := hsupp
    congr 1
    set m := t + 1 - d - a with hm
    have hn : t + 1 - d = a + m := by omega
    have hsplit : ∀ y z, law ε d y * lawFrom ε a m z * Kop ε t g d y z =
        1 / ((t : ℝ) + 1) * ((d : ℝ) * (lawFrom ε a m z * (law ε d y *
          (upProb ε d y * g (d + 1) (y + 1) z + (1 - upProb ε d y) * g (d + 1) y z))) +
        ((t + 1 - d : ℕ) : ℝ) * (law ε d y * (lawFrom ε a m z *
          (upProb ε (a + m) z * g d y (z + 1) + (1 - upProb ε (a + m) z) * g d y z)))) := by
      intro y z; unfold Kop; rw [hn]; ring
    unfold Inner
    rw [← hm, Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => hsplit y z))]
    have hsum : (∑ y ∈ range (t + 2), ∑ z ∈ range (t + 2),
        1 / ((t : ℝ) + 1) * ((d : ℝ) * (lawFrom ε a m z * (law ε d y *
          (upProb ε d y * g (d + 1) (y + 1) z + (1 - upProb ε d y) * g (d + 1) y z))) +
        ((t + 1 - d : ℕ) : ℝ) * (law ε d y * (lawFrom ε a m z *
          (upProb ε (a + m) z * g d y (z + 1) + (1 - upProb ε (a + m) z) * g d y z))))) =
        1 / ((t : ℝ) + 1) * ((d : ℝ) * (∑ y ∈ range (t + 2), ∑ z ∈ range (t + 2),
          lawFrom ε a m z * (law ε d y *
          (upProb ε d y * g (d + 1) (y + 1) z + (1 - upProb ε d y) * g (d + 1) y z))) +
        ((t + 1 - d : ℕ) : ℝ) * (∑ y ∈ range (t + 2), ∑ z ∈ range (t + 2),
          law ε d y * (lawFrom ε a m z *
          (upProb ε (a + m) z * g d y (z + 1) + (1 - upProb ε (a + m) z) * g d y z)))) := by
      simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hsum, join_part ε hd1 (by omega) (by omega) g, out_part ε hd1 (by omega) (by omega) g,
      show t + 1 + 2 = t + 2 + 1 by omega, show t + 1 + 1 - (d + 1) - a = m by omega,
      show t + 1 + 1 - d - a = m + 1 by omega]
    have hc : ((t + 1 - d : ℕ) : ℝ) = (t : ℝ) + 1 - d := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc]
    have : (t : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · have h0 : stLaw (a + 1) (t - a) d = 0 := by
      rcases Nat.lt_or_ge d 1 with h | h
      · obtain rfl : d = 0 := by omega
        exact stLaw_zero_size _ _
      · exact stLaw_eq_zero_of_lt _ (by omega)
    rw [h0, zero_mul, zero_mul]

/-- The product side moves by `Kop` too. -/
theorem RS_succ (ε : ℝ) {a t : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) (g : ℕ → ℕ → ℕ → ℝ) :
    RS ε a (t + 1) g = RS ε a t (Kop ε t g) := by
  unfold RS
  congr 1
  rw [Finset.sum_congr rfl (fun d hd => inner_step ε ha1 hat d (Finset.mem_range.1 hd) g)]
  have hv : ((a + 1 : ℕ) : ℝ) + ((t - a : ℕ) : ℝ) = (t : ℝ) + 1 := by
    rw [Nat.cast_sub hat]; push_cast; ring
  rw [show t + 1 + 2 = (t + 2) + 1 by omega, show t + 1 - a = (t - a) + 1 by omega]
  refine dual_sum (stLaw (a + 1) (t - a)) (stLaw (a + 1) (t - a + 1))
    (fun d => (d : ℝ) / ((t : ℝ) + 1)) (fun d => Inner ε a (t + 1) d g) (t + 2) ?_ ?_ ?_
  · simp [stLaw_zero_size]
  · intro b
    simp only [stLaw]
    rw [hv]
    push_cast
    ring
  · exact stLaw_eq_zero_of_lt _ (by omega)

/-- The tree side equals the product side, for every test function. -/
theorem TS_eq_RS (ε : ℝ) {a t : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) :
    ∀ g : ℕ → ℕ → ℕ → ℝ, TS ε a t g = RS ε a t g := by
  induction t, hat using Nat.le_induction with
  | base => intro g; rw [TS_base ε ha1, RS_base ε a]
  | succ t hat ih => intro g; rw [TS_succ ε ha1 hat, RS_succ ε ha1 hat, ih]

/-! ### The joint law and the decomposition of `f_N(m)` -/

theorem TS_indicator (ε : ℝ) (a t : ℕ) (P : ℕ → ℕ → ℕ → Prop) [∀ d y z, Decidable (P d y z)] :
    TS ε a t (fun d y z => if P d y z then 1 else 0) =
      rrtProb (fun _ => ε) t (fun _ T μ => firstAt μ a ∧
        P (subtreeSize T a) (evenIn T μ a) (oddOut T μ a)) := by
  unfold TS rrtProb
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ =>
    Finset.sum_congr rfl (fun μ _ => ?_)))
  by_cases hf : firstAt μ a <;> by_cases hP : P (subtreeSize T a) (evenIn T μ a) (oddOut T μ a) <;>
    simp [hf, hP]

/-- **Lemma 3.3 (`lem:firstmark`), the joint law at the first flip.** For the first marked vertex
`V = j` (Lean `a = j - 1`, `1 ≤ a ≤ t`, `N = t + 1`), its family `S` (`|S| = d`), the number `y`
of even vertices of `S` and the number `z` of odd vertices outside `S`:
`P(V = j, |S| = d, evenIn = y, oddOut = z) = ε(1-ε)^{j-2} β_j(d) P(Y_d = y) P(Z^{(j)}_{N-d} = z)`
with `Y_d ~ M^{[1]}_d` (`law ε d`) and `Z^{(j)}_{N-d} ~ M^{[j-1]}_{N-d}` (`lawFrom ε (j-1)`). -/
theorem rrt_firstFlip_joint (ε : ℝ) {a t : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) (d y z : ℕ) :
    rrtProb (fun _ => ε) t (fun _ T μ => firstAt μ a ∧ (subtreeSize T a = d ∧
      evenIn T μ a = y ∧ oddOut T μ a = z)) =
      ε * (1 - ε) ^ (a - 1) * stLaw (a + 1) (t - a) d * law ε d y *
        lawFrom ε a (t + 1 - d - a) z := by
  rw [← TS_indicator ε a t (fun d' y' z' => d' = d ∧ y' = y ∧ z' = z), TS_eq_RS ε ha1 hat]
  unfold RS Inner
  -- the factor of the `d`-th term vanishes outside the ranges
  have hzero : ¬ (d < t + 2 ∧ y < t + 2 ∧ z < t + 2) →
      stLaw (a + 1) (t - a) d * law ε d y * lawFrom ε a (t + 1 - d - a) z = 0 := by
    intro h
    by_cases hd : d < t + 2
    · by_cases hy : y < t + 2
      · have hz : t + 2 ≤ z := by omega
        rw [lawFrom_eq_zero ε a (by omega), mul_zero]
      · rcases Nat.lt_or_ge d 1 with h0 | h0
        · obtain rfl : d = 0 := by omega
          rw [stLaw_zero_size]; ring
        · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          rw [law_eq_zero ε (show d' + 1 ≤ y by omega)]; ring
    · rw [stLaw_eq_zero_of_lt _ (show t - a + 1 < d by omega)]; ring
  by_cases hin : d < t + 2 ∧ y < t + 2 ∧ z < t + 2
  · rw [Finset.sum_eq_single_of_mem d (Finset.mem_range.2 hin.1) (fun d' _ hd' => by simp [hd']),
      Finset.sum_eq_single_of_mem y (Finset.mem_range.2 hin.2.1) (fun y' _ hy' => by simp [hy']),
      Finset.sum_eq_single_of_mem z (Finset.mem_range.2 hin.2.2) (fun z' _ hz' => by simp [hz'])]
    simp only [and_self, if_true, mul_one]
    ring
  · have hR : ε * (1 - ε) ^ (a - 1) * stLaw (a + 1) (t - a) d * law ε d y *
        lawFrom ε a (t + 1 - d - a) z =
        ε * (1 - ε) ^ (a - 1) * (stLaw (a + 1) (t - a) d * law ε d y *
          lawFrom ε a (t + 1 - d - a) z) := by ring
    rw [hR, hzero hin, mul_zero]
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero (fun d' hd' => ?_)
    rw [Finset.sum_eq_zero (fun y' hy' => Finset.sum_eq_zero (fun z' hz' => ?_)), mul_zero]
    by_cases h : d' = d ∧ y' = y ∧ z' = z
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact absurd ⟨Finset.mem_range.1 hd', Finset.mem_range.1 hy', Finset.mem_range.1 hz'⟩ hin
    · simp [h]

/-- `M_N` splits at the family of `a`: the odd vertices of `𝒯_a` are those that are not even. -/
theorem oddCount_split {t : ℕ} (T : IncTree t) (μ : Word t) (a : ℕ) :
    oddCount T μ = subtreeSize T a - evenIn T μ a + oddOut T μ a := by
  have hle : evenIn T μ a ≤ subtreeSize T a := by
    unfold evenIn subtreeSize
    exact Finset.card_le_card (fun u hu => by
      rw [Finset.mem_filter] at hu ⊢; exact ⟨hu.1, hu.2.1⟩)
  have hsum : oddCount T μ + evenIn T μ a = subtreeSize T a + oddOut T μ a := by
    unfold oddCount evenIn subtreeSize oddOut
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    by_cases hin : ∃ w ∈ anc T u, (w : ℕ) = a <;>
      rcases Nat.mod_two_eq_zero_or_one (flips T μ u) with h | h <;> simp [hin, h]
  omega

/-- Without a mark every vertex is even, so `M_N = 0`. -/
theorem oddCount_of_noMark {t : ℕ} (T : IncTree t) {μ : Word t} (h : noMark μ) :
    oddCount T μ = 0 := by
  unfold oddCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _
  have : flips T μ u = 0 := by
    unfold flips
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _
    rw [h w]; simp
  rw [this]; simp

/-- Events that ignore the root sign: `P(X_1 = +, E) = P(E)/2`. -/
theorem rrtProb_sTrue (q : ℕ → ℝ) (t : ℕ) (E : IncTree t → Word t → Prop)
    [∀ T μ, Decidable (E T μ)] :
    rrtProb q t (fun s T μ => s = true ∧ E T μ) = rrtProb q t (fun _ T μ => E T μ) / 2 := by
  unfold rrtProb
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [true_and, Bool.false_eq_true, false_and, if_false, Finset.sum_const_zero, add_zero]
  ring

/-- `P(d - Y_d + Z^{(j)}_{N-d} = m)` for independent `Y_d ~ M^{[1]}_d` and
`Z^{(j)}_{N-d} ~ M^{[j-1]}_{N-d}` (`j = a + 1`, `N = t + 1`). -/
noncomputable def convYZ (ε : ℝ) (a t d m : ℕ) : ℝ :=
  ∑ y ∈ range (t + 2), ∑ z ∈ range (t + 2),
    law ε d y * lawFrom ε a (t + 1 - d - a) z * if d - y + z = m then 1 else 0

/-- **Lemma 3.3 (`lem:firstmark`), the decomposition of `f_N(m)`.** For `m ≥ 1` and `N = t + 1`:
`f_N(m) = ∑_{j=2}^{N} ε(1-ε)^{j-2} ∑_{d} β_j(d) P(d - Y_d + Z^{(j)}_{N-d} = m)`, where
`f_N(m) = P₊(M_N = m) = law ε N m`, `j = a + 1`, `β_j(d) = stLaw j (N - j) d`, and `Y_d`,
`Z^{(j)}_{N-d}` are independent (`convYZ`). The sum over `d` runs over `0 ≤ d ≤ N`; the terms
outside the paper's range `1 ≤ d ≤ N - j + 1` vanish. -/
theorem rrt_fN_decomp (ε : ℝ) (t : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    law ε (t + 1) m = ∑ a ∈ Icc 1 t, ε * (1 - ε) ^ (a - 1) *
      ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * convYZ ε a t d m := by
  have h1 : law ε (t + 1) m = rrtProb (fun _ => ε) t (fun _ T μ => oddCount T μ = m) := by
    have := rrt_oddCount_law ε t m
    rw [rrtProb_sTrue (fun _ => ε) t (fun T μ => oddCount T μ = m)] at this
    linarith
  rw [h1]
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = Icc 1 t := ⟨_, rfl⟩
  rw [← hS]
  rw [rrtProb_congr _ t _ (fun _ T μ => ∃ a ∈ S, firstAt μ a ∧
      subtreeSize T a - evenIn T μ a + oddOut T μ a = m) (fun _ T μ => by
    constructor
    · intro h
      have hnm : ¬ noMark μ := fun hn => by rw [oddCount_of_noMark T hn] at h; omega
      obtain ⟨a, ha, hf⟩ := exists_firstAt hnm
      exact ⟨a, hS ▸ ha, hf, by rw [← oddCount_split]; exact h⟩
    · rintro ⟨a, _, _, h⟩
      rw [oddCount_split T μ a]; exact h)]
  rw [rrtProb_exists (fun _ => ε) t S (fun a _ T μ => firstAt μ a ∧
      subtreeSize T a - evenIn T μ a + oddOut T μ a = m)
    (fun _ _ _ a b _ _ ha hb => firstAt_unique ha.1 hb.1)]
  subst hS
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_Icc] at ha
  rw [← TS_indicator ε a t (fun d y z => d - y + z = m), TS_eq_RS ε ha.1 ha.2]
  rfl

end RRT
end Kagey131.PaperD
