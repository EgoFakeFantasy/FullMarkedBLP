import FullMarkedBLP.NativeOwnerMark

namespace FullMarkedBLP

theorem sorted_consecutive_entry {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {i y : Nat} (hi : xs[i]? = some y) (hm : y + 1 ∈ xs) :
    xs[i + 1]? = some (y + 1) := by
  obtain ⟨hb, hv⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hm
  have hij : i < j := by
    by_cases he : i = j
    · subst j; omega
    · by_cases he' : j < i
      · have hh := List.pairwise_iff_getElem.mp hs j i hj hb he'
        omega
      · omega
  have he : i + (j - i) = j := by omega
  have hspace := sorted_index_spacing hs i (j - i) hb (by omega)
  simp only [he] at hspace
  have hj' : j = i + 1 := by omega
  subst j
  exact List.getElem?_eq_some_iff.mpr ⟨hj, hjv⟩

theorem nativeTop_target_entry {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    {j : Nat} (hj : j ≤ sources.length) :
    (nativeTop row r sources).core[row.core.length - 1 + sources.length + j]? = some (r + j) := by
  induction j with
  | zero =>
    have hv := valid r row hr
    have hend : row.core[row.core.length - 1]? = some r := by
      simpa [List.getLast?_eq_getElem?] using hv.2.2.1
    have hf : sources.filter (· < r) = sources := by
      apply List.filter_eq_self.mpr
      intro x hx
      simpa using nativeSources_below_owner valid hr h x hx
    have hrank := nativeTop_rank_exact valid hr h (Nat.le_refl r)
    rw [hf, sorted_rank_at_index hv.1 hend] at hrank
    have hm := (nativeTop_core_mem row r sources r).mpr
      (Or.inl (List.mem_of_getLast? hv.2.2.1))
    simpa [hrank] using sorted_get_at_rank (nativeTop_sorted row r sources).1 hm
  | succ j ih =>
    have he := ih (by omega)
    have hm : r + j + 1 ∈ (nativeTop row r sources).core := by
      apply (nativeTop_core_mem row r sources _).mpr
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    simpa [Nat.add_assoc] using sorted_consecutive_entry (nativeTop_sorted row r sources).1 he hm

theorem native_target_predecessor {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r j : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : native a r = some (b, sources))
    (hne : sources ≠ []) (hj : j ≤ sources.length) :
    predecessor b (r + j) =
      (nativeTop row r sources).core[row.core.length - (row.step + 1) + j]? := by
  unfold native at hn
  rw [hr] at hn
  dsimp only [Bind.bind, Option.bind] at hn
  obtain ⟨ss, hs, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨block, hb, hn⟩ := Option.bind_eq_some_iff.mp hn
  change some (_, ss) = some (b, sources) at hn
  cases Option.some.inj hn
  have hl := nativeBlock_length hb
  have hi : j < block.length := by omega
  simp only [predecessor, native_block_rowAt hr hi,
    List.getElem?_eq_getElem hi, Option.bind_some]
  exact nativeBlock_actual_p valid hr hs hne hb j hi

theorem nativeTop_target_mark {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r j : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hs : nativeSources a r = some sources)
    (hj : j < sources.length) : r + j ∈ (nativeTop row r sources).marks := by
  have hnm : r + j ∉ sources := by
    intro hm
    have hh := nativeSources_below_owner valid hr hs (r + j) hm
    omega
  simp only [nativeTop, mem_canonicalColumns, List.mem_filter]
  constructor
  · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩))
  · simp [hnm, show j ≠ sources.length by omega]

/-- Every newly introduced top-row mark has the actual one-step p-trace. -/
theorem native_top_target_markTrace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r j p : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hs : nativeSources a r = some sources)
    (hn : native a r = some (b, sources)) (hj : j < sources.length)
    (hp : predecessor b (r + j) = some p) :
    MarkTrace b (r + sources.length) (r + j) [r + j, p] := by
  have hne : sources ≠ [] := by intro hh; simp [hh] at hj
  have hv := valid r row hr
  have hl := Row.step_lt_length hv.2.2.2
  have hsrc := native_target_predecessor valid hr hn hne (Nat.le_of_lt hj)
  have hi : row.core.length - 1 + sources.length + j -
      (nativeTop row r sources).step = row.core.length - (row.step + 1) + j := by
    change _ - (row.step + sources.length) = _; omega
  refine ⟨nativeTop row r sources, row.core.length - 1 + sources.length + j, p,
    native_top_rowAt hr hn hne, nativeTop_target_mark valid hr hs hj, ?_,
    nativeTop_target_entry valid hr hs (Nat.le_of_lt hj), ?_, ?_⟩
  · change row.step + sources.length ≤ _; omega
  · rw [hi, ← hsrc]; exact hp
  · exact Trace.next (predecessor_lt (native_preserves_coreValid valid hn) hp) hp Trace.stop

theorem native_top_new_marks_have_trace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r j : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hs : nativeSources a r = some sources)
    (hn : native a r = some (b, sources)) (hj : j < sources.length) :
    ∃ p, MarkTrace b (r + sources.length) (r + j) [r + j, p] := by
  have hrb := rowAt_bounds hr
  have hlen := native_length hn
  obtain ⟨target, ht⟩ := rowAt_exists (a := b) (r := r + j) (by omega) (by omega)
  have hv := native_preserves_coreValid valid hn (r + j) target ht
  have hl := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := target.core) (k := target.step + 1) (by omega) (by omega)
  have he : predecessor b (r + j) = some p := by
    simpa only [predecessor, ht, Option.bind_some, Row.p] using hp
  exact ⟨p, native_top_target_markTrace valid hr hs hn hj he⟩

end FullMarkedBLP


