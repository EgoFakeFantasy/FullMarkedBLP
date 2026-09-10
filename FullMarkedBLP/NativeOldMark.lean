import FullMarkedBLP.NativeTargetIndex

namespace FullMarkedBLP

theorem nativeTop_low_entry {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p x k : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p)
    (h : nativeSources a r = some sources) (hx : row.core[k]? = some x)
    (hxp : x ≤ p) : (nativeTop row r sources).core[k]? = some x := by
  have hv := valid r row hr
  have hm := List.mem_iff_getElem?.mpr ⟨k, hx⟩
  have hxr := core_entry_le_owner hv hm
  have hf : sources.filter (· < x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro y hy
    have hb := nativeSources_above_p valid hr hp h y hy
    simp; omega
  have hrank := nativeTop_rank_exact valid hr h hxr
  simp only [hf, List.length_nil, Nat.add_zero, sorted_rank_at_index hv.1 hx] at hrank
  have htm := (nativeTop_core_mem row r sources x).mpr (Or.inl hm)
  simpa only [hrank] using sorted_get_at_rank (nativeTop_sorted row r sources).1 htm

theorem nativeTop_old_mark_entry {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y k : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (h : nativeSources a r = some sources) (hy : y ∈ row.marks)
    (hk : row.core[k]? = some y) :
    (nativeTop row r sources).core[k + sources.length]? = some y := by
  have hv := valid r row hr
  have hym := List.mem_iff_getElem?.mpr ⟨k, hk⟩
  have hf : sources.filter (· < y) = sources := by
    apply List.filter_eq_self.mpr
    intro x hx
    simpa using nativeSources_before_marks valid hr hm h x hx y hy
  have hrank := nativeTop_rank_exact valid hr h (Nat.le_of_lt (hm.2 y hy).1)
  rw [hf, sorted_rank_at_index hv.1 hk] at hrank
  have htm := (nativeTop_core_mem row r sources y).mpr (Or.inl hym)
  simpa only [hrank] using sorted_get_at_rank (nativeTop_sorted row r sources).1 htm

theorem step_source_le_p {row : Row} {r k y x p : Nat}
    (hv : row.CoreValid r) (hy : row.core[k]? = some y)
    (hx : row.core[k - row.step]? = some x) (hp : row.p = some p) : x ≤ p := by
  have hl := Row.step_lt_length hv.2.2.2
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  obtain ⟨hk, _⟩ := List.getElem?_eq_some_iff.mp hy
  obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hpi
  by_cases he : k - row.step = row.core.length - (row.step + 1)
  · have hv' : x = p := by simpa only [he, hjv] using hiv.symm
    omega
  · have hh := List.pairwise_iff_getElem.mp hv.1 (k - row.step)
      (row.core.length - (row.step + 1)) hi hj (by omega)
    omega

theorem nativeTop_old_mark_mem {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (hs : nativeSources a r = some sources) (hy : y ∈ row.marks) :
    y ∈ (nativeTop row r sources).marks := by
  have hyr := (hm.2 y hy).1
  have hnm : y ∉ sources := by
    intro hh
    have hb := nativeSources_before_marks valid hr hm hs y hh y hy
    omega
  simp only [nativeTop, mem_canonicalColumns, List.mem_filter]
  exact ⟨List.mem_append.mpr (Or.inl hy), by simp [hnm, show y ≠ r + sources.length by omega]⟩

theorem native_top_old_markTrace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y : Nat} {row : Row} {sources xs : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (hs : nativeSources a r = some sources)
    (hn : native a r = some (b, sources)) (hne : sources ≠ [])
    (ht : MarkTrace a r y xs) : MarkTrace b (r + sources.length) y xs := by
  obtain ⟨old, k, x, ho, hy, hk, hky, hkx, htrace⟩ := ht
  have he := Option.some.inj (ho.symm.trans hr)
  subst old
  have hv := valid r row hr
  have hl := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  have hp' : row.p = some p := hp
  have hxp := step_source_le_p hv hky hkx hp'
  refine ⟨nativeTop row r sources, k + sources.length, x, native_top_rowAt hr hn hne,
    nativeTop_old_mark_mem valid hr hm hs hy, ?_,
    nativeTop_old_mark_entry valid hr hm hs hy hky, ?_, ?_⟩
  · change row.step + sources.length ≤ _; omega
  · have heq : k + sources.length - (nativeTop row r sources).step = k - row.step := by
      change _ - (row.step + sources.length) = _; omega
    rw [heq]
    exact nativeTop_low_entry valid hr hp' hs hkx hxp
  · exact native_prefix_trace valid hn htrace (hm.2 y hy).1

theorem native_top_all_marks_have_trace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (traces : ∀ y ∈ row.marks, ∃ xs, MarkTrace a r y xs)
    (hs : nativeSources a r = some sources)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) :
    ∀ y ∈ (nativeTop row r sources).marks, ∃ xs, MarkTrace b (r + sources.length) y xs := by
  intro y hy
  simp only [nativeTop, mem_canonicalColumns, List.mem_filter] at hy
  rcases List.mem_append.mp hy.1 with hold | hnew
  · obtain ⟨xs, ht⟩ := traces y hold
    exact ⟨xs, native_top_old_markTrace valid hr hm hs hn hne ht⟩
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hnew
    have hj' : j < sources.length := List.mem_range.mp hj
    obtain ⟨p, ht⟩ := native_top_new_marks_have_trace valid hr hs hn hj'
    exact ⟨[r + j, p], by simpa only [he] using ht⟩

end FullMarkedBLP


