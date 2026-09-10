import Mathlib.SetTheory.Ordinal.Basic

namespace FullMarkedBLP

/-- If every allowed set is at least as large as the entire index type,
there are pairwise distinct representatives. Choose in a cardinal-sized
well-order, where every earlier segment has strictly smaller cardinality. -/
theorem exists_injective_choice_of_cardinal_bound {I B : Type u}
    (allowed : I → Set B) (large : ∀ i, Cardinal.mk I ≤ Cardinal.mk (allowed i)) :
    ∃ choice : I → B, Function.Injective choice ∧ ∀ i, choice i ∈ allowed i := by
  classical
  obtain ⟨order, wellFounded, initial⟩ := Cardinal.exists_ord_eq_type_lt I
  letI : LinearOrder I := order
  letI : WellFoundedLT I := wellFounded
  have fresh : ∀ (i : I) (previous : Set.Iio i → B),
      ∃ y : allowed i, y.val ∉ Set.range previous := by
    intro i previous
    by_contra failure
    have included : allowed i ⊆ Set.range previous := by
      intro y hy
      by_contra missing
      exact failure ⟨⟨y, hy⟩, missing⟩
    have small : Cardinal.mk (Set.Iio i) < Cardinal.mk (allowed i) :=
      (Cardinal.mk_Iio_lt i initial).trans_le (large i)
    have reverse : Cardinal.mk (allowed i) ≤ Cardinal.mk (Set.Iio i) :=
      (Cardinal.mk_le_mk_of_subset included).trans Cardinal.mk_range_le
    exact (not_le_of_gt small) reverse
  let step (i : I) (previous : ∀ k, k < i → allowed k) : allowed i :=
    Classical.choose (fresh i (fun k => (previous k.val k.property).val))
  let picked : ∀ i, allowed i := wellFounded_lt.fix step
  have pickedFresh : ∀ i k, k < i → (picked i).val ≠ (picked k).val := by
    intro i k below same
    have eq : picked i = step i (fun k _ => picked k) := WellFounded.fix_eq wellFounded_lt step i
    have excluded := Classical.choose_spec (fresh i (fun a : Set.Iio i => (picked a.val).val))
    apply excluded
    refine ⟨⟨k, below⟩, ?_⟩
    rw [eq] at same
    exact same.symm
  refine ⟨fun i => (picked i).val, ?_, fun i => (picked i).property⟩
  intro i k same
  rcases lt_trichotomy i k with below | equal | above
  · exact False.elim (pickedFresh k i below same.symm)
  · exact equal
  · exact False.elim (pickedFresh i k above same)

end FullMarkedBLP
