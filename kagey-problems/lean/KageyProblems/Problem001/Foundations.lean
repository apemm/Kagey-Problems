import KageyProblems.Problem001

/-!
# Basic operations on Problem 001 blackouts

Infrastructure for the other Problem 001 files, not a formalization of the
three-row or four-row theorems.

Validity is downward closed in the blackout and depends only on points in the grid.
It also restricts to smaller grids. The final lemma transports presentation
injectivity along any embedding of the point type, provided the rectangle family
is transported too; arbitrary relabelings need not preserve geometric rectangles.
-/

namespace Kagey001

/-- Revealing more points preserves validity. -/
theorem Valid.mono {n m : ℕ} {S T : Finset Pt}
    (hS : Valid n m S) (hTS : T ⊆ S) : Valid n m T := by
  rw [valid_iff_hitting] at hS ⊢
  intro A hA B hB hne
  obtain ⟨x, hx, hxS⟩ := hS A hA B hB hne
  exact ⟨x, hx, fun hxT => hxS (hTS hxT)⟩

/-- A collision persists when more points are blacked out. -/
theorem not_valid_of_subset {n m : ℕ} {S T : Finset Pt}
    (hS : ¬ Valid n m S) (hST : S ⊆ T) : ¬ Valid n m T :=
  fun hT => hS (hT.mono hST)

/-- With every corner visible, the presentation is the rectangle itself. -/
theorem valid_empty (n m : ℕ) : Valid n m ∅ := by
  intro A _ B _ h
  simpa [pres] using h

/-- Points outside the ambient grid have no effect on a presentation. -/
theorem pres_inter_grid {n m : ℕ} (S C : Finset Pt)
    (hC : C ⊆ grid n m) : pres (S ∩ grid n m) C = pres S C := by
  ext x
  simp only [pres, Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun hxS => h ⟨hxS, hC hx⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun h' => h h'.1⟩

/-- `Valid` does not itself require the blackout to be contained in the grid. -/
theorem valid_inter_grid_iff (n m : ℕ) (S : Finset Pt) :
    Valid n m (S ∩ grid n m) ↔ Valid n m S := by
  constructor
  · intro h A hA B hB hp
    apply h A hA B hB
    simpa only [pres_inter_grid S A hA.2, pres_inter_grid S B hB.2] using hp
  · intro h
    exact h.mono Finset.inter_subset_left

/-- Inclusion of the upper-left grids. -/
theorem grid_mono {n m n' m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    grid n m ⊆ grid n' m' := by
  intro p hp
  rw [mem_grid] at hp ⊢
  exact ⟨hp.1, le_trans hp.2.1 (by exact_mod_cast hm),
    hp.2.2.1, le_trans hp.2.2.2 (by exact_mod_cast hn)⟩

/-- Every rectangle in a smaller grid is also a rectangle in a larger grid. -/
theorem rects_mono {n m n' m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    Rects n m ⊆ Rects n' m' :=
  fun _ hC => ⟨hC.1, Finset.Subset.trans hC.2 (grid_mono hn hm)⟩

/-- Validity on a larger grid implies validity on a smaller grid. -/
theorem Valid.restrict_grid {n m n' m' : ℕ} {S : Finset Pt}
    (hS : Valid n' m' S) (hn : n ≤ n') (hm : m ≤ m') : Valid n m S :=
  fun A hA B hB h => hS A (rects_mono hn hm hA) B (rects_mono hn hm hB) h

/-- Restrict a valid blackout and its grid simultaneously. -/
theorem Valid.inter_grid {n m n' m' : ℕ} {S : Finset Pt}
    (hS : Valid n' m' S) (hn : n ≤ n') (hm : m ≤ m') :
    Valid n m (S ∩ grid n m) :=
  (hS.restrict_grid hn hm).mono Finset.inter_subset_left

/-- A generic transport lemma for finite-set presentations. The target family
must be the image of the source family; no geometric preservation is assumed. -/
theorem presentation_injective_map_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (F : Set (Finset α)) (S : Finset α) :
    Set.InjOn (fun C => C \ S) F ↔
      Set.InjOn (fun C => C \ S.map f) ((Finset.map f) '' F) := by
  constructor
  · rintro h _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hp
    apply congrArg (Finset.map f)
    apply h hA hB
    apply Finset.map_injective f
    simpa only [Finset.map_sdiff] using hp
  · intro h A hA B hB hp
    apply Finset.map_injective f
    apply h ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    simpa only [Finset.map_sdiff] using congrArg (Finset.map f) hp

end Kagey001
