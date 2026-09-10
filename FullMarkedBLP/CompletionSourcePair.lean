import FullMarkedBLP.CompletionTargetTrace

namespace FullMarkedBLP

/-- A source inserted in a fixed old gap has its old-gap rank plus its source rank. -/
theorem completeMarkRow_source_entry {row : Row} {y i left right x : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hl : row.core[i]? = some left) (hr : row.core[i + 1]? = some right)
    (hgap : ∀ z ∈ sources, left < z ∧ z < right)
    (hst : ∀ z ∈ sources, z ≤ y)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hx : x ∈ sources) :
    (completeMarkRow row y sources).core[i + 1 + (sources.filter (· < x)).length]? = some x := by
  have hdis : ∀ z ∈ sources, z ∉ row.core := by
    intro z hz
    exact between_adjacent_not_mem hc hl hr (hgap z hz).1 (hgap z hz).2
  have htf : (((List.range sources.length).map (fun j => y + 1 + j)).filter (· < x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro z hz
    have hb := (mem_after_range y sources.length z).mp hz
    have hxy := hst x hx
    simp; omega
  have hold := rank_between_adjacent hc hl hr (hgap x hx).1 (hgap x hx).2
  have hrank := completeMarkRow_rank (hc.imp (fun h => Nat.ne_of_lt h)) hs hdis hst ht (x := x)
  simp only [htf, List.length_nil, Nat.add_zero, hold] at hrank
  have hm := (completeMarkRow_core_mem row y sources x).mpr (Or.inr (Or.inl hx))
  simpa only [hrank] using sorted_get_at_rank (completeMarkRow_sorted row y sources).1 hm

/-- Matching gap and step indices identifies each new marked pair exactly. -/
theorem completeMarkRow_new_pair {row : Row} {y k left right x : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hl : row.core[k - row.step]? = some left)
    (hr : row.core[k - row.step + 1]? = some right)
    (hgap : ∀ z ∈ sources, left < z ∧ z < right)
    (hst : ∀ z ∈ sources, z < y)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hx : x ∈ sources) :
    ∃ j, (completeMarkRow row y sources).step ≤ j ∧
      (completeMarkRow row y sources).core[j]? = some (y + ((sources.filter (· < x)).length + 1)) ∧
      (completeMarkRow row y sources).core[j - (completeMarkRow row y sources).step]? = some x := by
  have hdis : ∀ z ∈ sources, z ∉ row.core := by
    intro z hz
    exact between_adjacent_not_mem hc hl hr (hgap z hz).1 (hgap z hz).2
  have hlt : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  refine ⟨k + sources.length + ((sources.filter (· < x)).length + 1), ?_, ?_, ?_⟩
  · change row.step + sources.length ≤ _; omega
  · exact completeMarkRow_targets_entry hc hs hdis ht hy hst (by omega)
  · have he : k + sources.length + ((sources.filter (· < x)).length + 1) -
        (completeMarkRow row y sources).step = k - row.step + 1 + (sources.filter (· < x)).length := by
      change _ - (row.step + sources.length) = _; omega
    rw [he]
    exact completeMarkRow_source_entry hc hs hl hr hgap (fun z hz => Nat.le_of_lt (hst z hz)) ht hx

/-- A parallel packet chain becomes the corresponding new literal MarkTrace. -/
theorem completion_new_markTrace {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {owner y k left right x : Nat} {row : Row} {sources xs : List Nat}
    (hrow : rowAt a owner = some row) (hs : sources.Nodup)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hl : row.core[k - row.step]? = some left)
    (hr : row.core[k - row.step + 1]? = some right)
    (hgap : ∀ z ∈ sources, left < z ∧ z < right)
    (hst : ∀ z ∈ sources, z < y)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hx : x ∈ sources) (hbound : y + sources.length < owner)
    (hpacket : Trace a x (y + ((sources.filter (· < x)).length + 1)) xs) :
    MarkTrace (a.set (owner - 1) (completeMarkRow row y sources)) owner
      (y + ((sources.filter (· < x)).length + 1)) xs := by
  obtain ⟨j, hj, hjy, hjx⟩ := completeMarkRow_new_pair (valid owner row hrow).1 hs hk hy hl hr hgap hst ht hx
  have hlt : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have hm : y + ((sources.filter (· < x)).length + 1) ∈ (completeMarkRow row y sources).marks := by
    simp only [completeMarkRow, mem_canonicalColumns, List.mem_append]
    apply Or.inr
    apply (mem_after_range y sources.length _).mpr
    exact ⟨by omega, by omega⟩
  refine ⟨completeMarkRow row y sources, j, x, rowAt_set_self hrow, hm, hj, hjy, hjx, ?_⟩
  exact trace_prefix valid hpacket (by omega : y + ((sources.filter (· < x)).length + 1) < owner)
    (fun i hi => (rowAt_set_other hrow (by omega : i ≠ owner)).symm)

end FullMarkedBLP

