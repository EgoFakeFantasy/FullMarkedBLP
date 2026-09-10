import FullMarkedBLP.NativeClosure

namespace FullMarkedBLP

/-- Deleting a larger entry of an increasing core leaves an earlier index intact. -/
theorem erase_greater_preserves_index {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {k y removed : Nat} (hy : xs[k]? = some y) (hlt : y < removed) :
    (xs.erase removed)[k]? = some y := by
  induction xs generalizing k with
  | nil => simp at hy
  | cons z zs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst y
      simp [Nat.ne_of_lt hlt]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hy
      have hm : y ∈ zs := List.mem_iff_getElem?.mpr ⟨k, hy⟩
      have hz := (List.pairwise_cons.mp hs).1 y hm
      have hn : z ≠ removed := by omega
      simpa [List.erase_cons, hn, Ne.symm hn] using ih (List.pairwise_cons.mp hs).2 hy

/-- Any one deletion shifts a retained entry left by at most one position. -/
theorem erase_index_bound {xs : List Nat} {k y removed : Nat}
    (hy : xs[k]? = some y) (hne : y ≠ removed) :
    ∃ j, k ≤ j + 1 ∧ (xs.erase removed)[j]? = some y := by
  induction xs generalizing k with
  | nil => simp at hy
  | cons z zs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst y
      exact ⟨0, by omega, by simp [hne]⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hy
      by_cases hz : z = removed
      · subst z
        exact ⟨k, by omega, by simpa using hy⟩
      · obtain ⟨j, hj, he⟩ := ih hy
        exact ⟨j + 1, by omega, by simpa [List.erase_cons, hz, Ne.symm hz] using he⟩

/-- The medium exception preserves old target positions and removes the new owner mark. -/
theorem nativeLower_medium_proper {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (h : nativeLower row owner true = some lower) : lower.ProperMarks (owner - 1) := by
  cases Option.some.inj h
  refine ⟨hm.1.sublist List.erase_sublist, ?_⟩
  intro y hy
  have hn : row.marks.Nodup := hm.1.imp (fun hh => Nat.ne_of_lt hh)
  have hy' := hn.mem_erase_iff.mp hy
  obtain ⟨hb, k, hk, he⟩ := hm.2 y hy'.2
  refine ⟨by omega, k, hk, ?_⟩
  exact erase_greater_preserves_index hv.1 he hb


/-- In a short row the e-source precedes every proper step-target position. -/
theorem short_source_before_mark {row : Row} {owner source y : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (hlen : row.core.length + 1 = 2 * row.step)
    (he : row.e = some source) (hy : y ∈ row.marks) : source < y := by
  obtain ⟨_, k, hk, hky⟩ := hm.2 y hy
  obtain ⟨hi, hiy⟩ := List.getElem?_eq_some_iff.mp hky
  unfold Row.e fromRight at he
  split at he
  next hb =>
    obtain ⟨hj, hjs⟩ := List.getElem?_eq_some_iff.mp he
    have hh := List.pairwise_iff_getElem.mp hv.1 (row.core.length - row.step) k hj hi (by omega)
    simpa [hjs, hiy] using hh
  next => simp at he

theorem nativeLower_short_proper {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (hlen : row.core.length + 1 = 2 * row.step)
    (h : nativeLower row owner false = some lower) : lower.ProperMarks (owner - 1) := by
  obtain ⟨source, he, hout⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj hout
  refine ⟨hm.1.sublist List.erase_sublist, ?_⟩
  intro y hy
  have hn : row.marks.Nodup := hm.1.imp (fun hh => Nat.ne_of_lt hh)
  have hy' := hn.mem_erase_iff.mp hy
  obtain ⟨hb, k, hk, hky⟩ := hm.2 y hy'.2
  have hs := short_source_before_mark hv hm hlen he hy'.2
  have ho := erase_greater_preserves_index hv.1 hky hb
  obtain ⟨j, hj, hje⟩ := erase_index_bound ho (Nat.ne_of_gt hs)
  exact ⟨by omega, j, by change row.step - 1 ≤ j; omega, hje⟩


/-- A target index is exactly the number of core entries strictly below it. -/
theorem sorted_rank_at_index {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {k y : Nat} (hy : xs[k]? = some y) : (xs.filter (· < y)).length = k := by
  induction xs generalizing k with
  | nil => simp at hy
  | cons z zs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst y
      have ht : zs.filter (· < z) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        have hh := (List.pairwise_cons.mp hs).1 x hx
        simp; omega
      simp [ht]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hy
      have hm : y ∈ zs := List.mem_iff_getElem?.mpr ⟨k, hy⟩
      have hz := (List.pairwise_cons.mp hs).1 y hm
      simp [hz, ih (List.pairwise_cons.mp hs).2 hy]

theorem target_position_iff_rank {row : Row} (hs : row.core.Pairwise (· < ·))
    {y : Nat} (hy : y ∈ row.core) :
    (∃ k, row.step ≤ k ∧ row.core[k]? = some y) ↔
      row.step ≤ (row.core.filter (· < y)).length := by
  constructor
  · rintro ⟨k, hk, he⟩
    simpa [sorted_rank_at_index hs he] using hk
  · intro h
    obtain ⟨k, he⟩ := List.mem_iff_getElem?.mp hy
    exact ⟨k, by simpa [sorted_rank_at_index hs he] using h, he⟩

end FullMarkedBLP
