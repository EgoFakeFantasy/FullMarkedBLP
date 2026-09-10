import FullMarkedBLP.NativeMarks

namespace FullMarkedBLP

/-- For every eligible row, e is no later than any proper marked target. -/
theorem eligible_source_le_mark {row : Row} {owner e y : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (helig : row.core.length ≤ 2 * row.step)
    (he : row.e = some e) (hy : y ∈ row.marks) : e ≤ y := by
  obtain ⟨_, k, hk, hky⟩ := hm.2 y hy
  obtain ⟨hi, hiy⟩ := List.getElem?_eq_some_iff.mp hky
  unfold Row.e fromRight at he
  split at he
  next hb =>
    obtain ⟨hj, hje⟩ := List.getElem?_eq_some_iff.mp he
    by_cases heq : row.core.length - row.step = k
    · have hh : e = y := by simpa only [heq, hiy] using hje.symm
      omega
    · have hh := List.pairwise_iff_getElem.mp hv.1 (row.core.length - row.step) k hj hi (by omega)
      rw [hje, hiy] at hh
      omega
  next => simp at he

theorem nativeSources_before_marks {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (h : nativeSources a r = some sources) :
    ∀ x ∈ sources, ∀ y ∈ row.marks, x < y := by
  unfold nativeSources at h
  rw [hr] at h
  dsimp only [Bind.bind, Option.bind] at h
  split at h
  next =>
    change some [] = some sources at h
    cases Option.some.inj h
    simp
  next helig =>
    obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
    intro x hx y hy
    have hb := nativeSourcesFuel_bounds valid h x hx
    have hm' := eligible_source_le_mark (valid r row hr) hm (by omega) he hy
    omega


/-- A duplicate-free subcollection cannot be longer than its containing list. -/
theorem nodup_subset_length {xs ys : List Nat} (hn : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp hn
    have hxy := hsub x (by simp)
    have hs : ∀ y ∈ xs, y ∈ ys.erase x := by
      intro y hy
      have hne : y ≠ x := by intro he; subst y; exact hx hy
      exact (List.mem_erase_of_ne hne).mpr (hsub y (List.mem_cons_of_mem x hy))
    have hh := ih ht hs
    rw [List.length_erase_of_mem hxy] at hh
    obtain ⟨i, hi, _⟩ := List.mem_iff_getElem.mp hxy
    simp only [List.length_cons]
    omega

/-- The t distinct new sources raise the old lower-column count by at least t. -/
theorem nativeTop_rank_bound {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {y : Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    (hbelow : ∀ x ∈ sources, x < y) :
    (row.core.filter (· < y)).length + sources.length ≤
      ((nativeTop row r sources).core.filter (· < y)).length := by
  have hc : row.core.Nodup := (valid r row hr).1.imp (fun hh => Nat.ne_of_lt hh)
  have hs : sources.Nodup := (nativeSources_decreasing valid h).imp (fun hh => Nat.ne_of_gt hh)
  have hn : (row.core.filter (· < y) ++ sources).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hc.sublist (List.filter_sublist), hs, ?_⟩
    intro x hx z hz he
    subst z
    exact nativeSources_disjoint valid hr h x hz (List.mem_filter.mp hx).1
  have hsub : ∀ x ∈ row.core.filter (· < y) ++ sources,
      x ∈ (nativeTop row r sources).core.filter (· < y) := by
    intro x hx
    apply List.mem_filter.mpr
    rcases List.mem_append.mp hx with hx | hx
    · have hh := List.mem_filter.mp hx
      exact ⟨(nativeTop_core_mem row r sources x).mpr (Or.inl hh.1), hh.2⟩
    · exact ⟨(nativeTop_core_mem row r sources x).mpr (Or.inr (Or.inl hx)), by simpa using hbelow x hx⟩
  simpa using nodup_subset_length hn hsub

theorem nativeTop_old_mark_position {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {y : Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (h : nativeSources a r = some sources) (hy : y ∈ row.marks) :
    ∃ k, (nativeTop row r sources).step ≤ k ∧
      (nativeTop row r sources).core[k]? = some y := by
  obtain ⟨_, k, hk, he⟩ := hm.2 y hy
  have hym : y ∈ row.core := List.mem_iff_getElem?.mpr ⟨k, he⟩
  apply (target_position_iff_rank (nativeTop_sorted row r sources).1
    ((nativeTop_core_mem row r sources y).mpr (Or.inl hym))).mpr
  have hb := nativeTop_rank_bound valid hr h (fun x hx => nativeSources_before_marks valid hr hm h x hx y hy)
  have ho := sorted_rank_at_index (valid r row hr).1 he
  change row.step + sources.length ≤ _
  omega


theorem nativeTop_new_mark_position {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {y : Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    (hy : r ≤ y) (hym : y ∈ (nativeTop row r sources).core) :
    ∃ k, (nativeTop row r sources).step ≤ k ∧
      (nativeTop row r sources).core[k]? = some y := by
  have hv := valid r row hr
  have hc : row.core.Nodup := hv.1.imp (fun hh => Nat.ne_of_lt hh)
  have hsub : ∀ x ∈ row.core.filter (· < r), x ∈ row.core.filter (· < y) := by
    intro x hx
    obtain ⟨hm, hb⟩ := List.mem_filter.mp hx
    exact List.mem_filter.mpr ⟨hm, by simp at hb ⊢; omega⟩
  have hmono := nodup_subset_length (hc.sublist List.filter_sublist) hsub
  have hend : row.core[row.core.length - 1]? = some r := by
    simpa [List.getLast?_eq_getElem?] using hv.2.2.1
  have hrank := sorted_rank_at_index hv.1 hend
  have hstep := Row.step_lt_length hv.2.2.2
  have hbound := nativeTop_rank_bound valid hr h
    (fun x hx => Nat.lt_of_lt_of_le (nativeSources_below_owner valid hr h x hx) hy)
  apply (target_position_iff_rank (nativeTop_sorted row r sources).1 hym).mpr
  change row.step + sources.length ≤ _
  omega

theorem nativeTop_actual_properMarks {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (h : nativeSources a r = some sources) :
    (nativeTop row r sources).ProperMarks (r + sources.length) := by
  refine ⟨(nativeTop_sorted row r sources).2, ?_⟩
  intro y hy
  refine ⟨nativeTop_marks_before_owner (fun x hx => (hm.2 x hx).1) y hy, ?_⟩
  have hym : y ∈ (nativeTop row r sources).core := by
    apply nativeTop_marks_in_core (row := row) (r := r) (sources := sources) _
      (List.mem_of_getLast? (valid r row hr).2.2.1) y hy
    intro x hx
    obtain ⟨_, k, _, he⟩ := hm.2 x hx
    exact List.mem_iff_getElem?.mpr ⟨k, he⟩
  have hcases := hy
  simp only [nativeTop, mem_canonicalColumns, List.mem_filter, List.mem_append,
    List.mem_map, List.mem_range] at hcases
  rcases hcases.1 with hold | ⟨i, hi, he⟩
  · exact nativeTop_old_mark_position valid hr hm h hold
  · exact nativeTop_new_mark_position valid hr h (by omega) hym

end FullMarkedBLP
