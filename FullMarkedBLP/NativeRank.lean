import FullMarkedBLP.NativePredecessor

namespace FullMarkedBLP

theorem canonical_filter_length {xs : List Nat} (hn : xs.Nodup) (test : Nat → Bool) :
    ((canonicalColumns xs).filter test).length = (xs.filter test).length := by
  have hc : (canonicalColumns xs).Nodup :=
    (canonicalColumns_sorted xs).imp (fun h => Nat.ne_of_lt h)
  apply Nat.le_antisymm
  · apply nodup_subset_length (hc.sublist List.filter_sublist)
    intro x hx
    simpa only [List.mem_filter, mem_canonicalColumns] using hx
  · apply nodup_subset_length (hn.sublist List.filter_sublist)
    intro x hx
    simpa only [List.mem_filter, mem_canonicalColumns] using hx

theorem nativeTop_inputs_nodup {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources) :
    (row.core ++ sources ++ (List.range sources.length).map (fun i => r + 1 + i)).Nodup := by
  have hc : row.core.Nodup := (valid r row hr).1.imp (fun h => Nat.ne_of_lt h)
  have hs : sources.Nodup := (nativeSources_decreasing valid h).imp (fun h => Nat.ne_of_gt h)
  have hb : (row.core ++ sources).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hc, hs, ?_⟩
    intro x hx y hy he
    subst y
    exact nativeSources_disjoint valid hr h x hy hx
  apply List.nodup_append.mpr
  refine ⟨hb, (after_range_sorted r sources.length).imp (fun h => Nat.ne_of_lt h), ?_⟩
  intro x hx y hy he
  have hyb := (mem_after_range r sources.length y).mp hy
  rcases List.mem_append.mp hx with hx | hx
  · have hh := core_entry_le_owner (valid r row hr) hx; omega
  · have hh := nativeSources_below_owner valid hr h x hx; omega

theorem nativeTop_rank_exact {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    {y : Nat} (hy : y ≤ r) :
    ((nativeTop row r sources).core.filter (· < y)).length =
      (row.core.filter (· < y)).length + (sources.filter (· < y)).length := by
  have ht : ((List.range sources.length).map (fun i => r + 1 + i)).filter (· < y) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hh := (mem_after_range r sources.length x).mp hx
    simp; omega
  change ((canonicalColumns _).filter _).length = _
  rw [canonical_filter_length (nativeTop_inputs_nodup valid hr h)]
  simp [List.filter_append, ht]

theorem sorted_get_at_rank {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {y : Nat} (hy : y ∈ xs) : xs[(xs.filter (· < y)).length]? = some y := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hy
  rw [sorted_rank_at_index hs hi]
  exact hi

#print axioms nativeTop_rank_exact



theorem nativeSources_above_p {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p)
    (h : nativeSources a r = some sources) : ∀ x ∈ sources, p < x := by
  unfold nativeSources at h
  rw [hr] at h
  dsimp only [Bind.bind, Option.bind] at h
  split at h
  next =>
    change some [] = some sources at h
    cases Option.some.inj h
    simp
  next =>
    rw [hp] at h
    dsimp only [Bind.bind, Option.bind] at h
    obtain ⟨e, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact fun x hx => (nativeSourcesFuel_bounds valid h x hx).1

/-- Insertion does not change the old p-column's index in the top core. -/
theorem nativeTop_old_p_entry {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p)
    (h : nativeSources a r = some sources) :
    (nativeTop row r sources).core[row.core.length - (row.step + 1)]? = some p := by
  have hv := valid r row hr
  have hple := fromRight_le_last hv.1 hv.2.2.1 (by omega : 0 < row.step + 1) hp
  have hfilter : sources.filter (· < p) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hh := nativeSources_above_p valid hr hp h x hx
    simp; omega
  have hi : row.core[row.core.length - (row.step + 1)]? = some p := by
    have hs := Row.step_lt_length hv.2.2.2
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hm : p ∈ row.core := List.mem_iff_getElem?.mpr ⟨_, hi⟩
  have htmem : p ∈ (nativeTop row r sources).core :=
    (nativeTop_core_mem row r sources p).mpr (Or.inl hm)
  have hget := sorted_get_at_rank (nativeTop_sorted row r sources).1 htmem
  have hrank := nativeTop_rank_exact valid hr h hple
  simp only [hfilter, List.length_nil, Nat.add_zero, sorted_rank_at_index hv.1 hi] at hrank
  simpa only [hrank] using hget

#print axioms nativeTop_old_p_entry
end FullMarkedBLP
