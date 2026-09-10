import FullMarkedBLP.CompletionEarlierMark

namespace FullMarkedBLP

theorem exists_source_at_rank {sources : List Nat} (hs : sources.Nodup)
    {j : Nat} (hj : j < sources.length) :
    ∃ x ∈ sources, (sources.filter (· < x)).length = j := by
  have hl := canonicalColumns_length hs
  have hi : j < (canonicalColumns sources).length := by omega
  let x := (canonicalColumns sources)[j]
  have hx : (canonicalColumns sources)[j]? = some x := by simp [hi, x]
  have hm : x ∈ sources := (mem_canonicalColumns x sources).mp (List.mem_iff_getElem?.mpr ⟨j, hx⟩)
  have hrank := sorted_rank_at_index (canonicalColumns_sorted sources) hx
  rw [canonical_filter_length hs] at hrank
  exact ⟨x, hm, hrank⟩

/-- Conditional row closure: interval geometry and actual parallel chains
are explicit obligations, not consequences asserted about the guard. -/
theorem completion_row_hasTraces {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y k left right : Nat} {row : Row} {sources : List Nat}
    (hrow : rowAt a r = some row) (hm : row.ProperMarks r)
    (oldTraces : row.HasTraces a) (hs : sources.Nodup)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hl : row.core[k - row.step]? = some left)
    (hr : row.core[k - row.step + 1]? = some right)
    (hgap : ∀ z ∈ sources, left < z ∧ z < right)
    (hst : ∀ z ∈ sources, z < y)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hbound : y + sources.length < r)
    (intervals : ∀ z ∈ row.marks, ∀ i x, row.step ≤ i →
      row.core[i]? = some z → row.core[i - row.step]? = some x →
      (x ≤ z ∧ z ≤ y ∧ ∀ w ∈ sources, x < w ∧ w < z) ∨
      (x ≤ y ∧ y + sources.length < z ∧ ∀ w ∈ sources, w < x))
    (packet : ∀ x ∈ sources, ∃ xs, Trace a x (y + ((sources.filter (· < x)).length + 1)) xs) :
    (completeMarkRow row y sources).HasTraces (a.set (r - 1) (completeMarkRow row y sources)) := by
  apply (row_hasTraces_iff (rowAt_set_self hrow)).mpr
  intro z hz
  have hdis : ∀ x ∈ sources, x ∉ row.core := by
    intro x hx
    exact between_adjacent_not_mem (valid r row hrow).1 hl hr (hgap x hx).1 (hgap x hx).2
  simp only [completeMarkRow, mem_canonicalColumns, List.mem_append] at hz
  rcases hz with hold | hnew
  · have hzm := (List.mem_filter.mp hold).1
    obtain ⟨i, x, xs, hi, hiz, hix, htrace⟩ := oldTraces z hzm
    exact ⟨xs, completion_old_markTrace valid hrow (hm.2 z hzm).1 hzm hi hiz hix htrace
      hs hdis ht (intervals z hzm i x hi hiz hix)⟩
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hnew
    obtain ⟨x, hx, hrank⟩ := exists_source_at_rank hs (List.mem_range.mp hj)
    obtain ⟨xs, htrace⟩ := packet x hx
    have hmark := completion_new_markTrace valid hrow hs hk hy hl hr hgap hst ht hx hbound htrace
    have heq : y + ((sources.filter (· < x)).length + 1) = z := by omega
    exact ⟨xs, by simpa only [heq] using hmark⟩

end FullMarkedBLP

