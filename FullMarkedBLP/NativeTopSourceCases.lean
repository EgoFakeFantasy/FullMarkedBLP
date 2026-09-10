import FullMarkedBLP.NativeTopInsertedIndices

namespace FullMarkedBLP

theorem native_source_rank_surjective {a : Pattern} {r j : Nat} {sources : List Nat}
    (hs : nativeSources a r = some sources) (hj : j < sources.length) :
    ∃ x ∈ sources, (sources.filter (· < x)).length = j := by
  have hlen := canonicalColumns_length (nativeSources_nodup_of_success hs)
  have hj' : j < (canonicalColumns sources).length := by omega
  let x := (canonicalColumns sources)[j]'hj'
  have hx : (canonicalColumns sources)[j]? = some x := List.getElem?_eq_getElem hj'
  have hrank := sorted_rank_at_index (canonicalColumns_sorted sources) hx
  rw [canonical_filter_length (nativeSources_nodup_of_success hs)] at hrank
  exact ⟨x, (mem_canonicalColumns x sources).mp (List.mem_of_getElem? hx), hrank⟩

/-- Exhaustive source-index cases for any literal full top step edge. -/
theorem nativeTop_edge_source_cases {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r k y : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hs : nativeSources a r = some sources)
    (hy : ((nativeTop row r sources).full (r + sources.length))[k + (nativeTop row r sources).step]? = some y) :
    k < row.core.length - row.step ∨
      (∃ x ∈ sources, k = row.core.length - row.step + (sources.filter (· < x)).length) ∨
      k = row.core.length - row.step + sources.length := by
  have hv := valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  have hbound := (List.getElem?_eq_some_iff.mp hy).1
  have hlen := nativeTop_actual_length valid hr hs
  have hstep : (nativeTop row r sources).step = row.step + sources.length := rfl
  simp only [Row.full, List.length_append, List.length_singleton, hlen, hstep] at hbound
  by_cases hlo : k < row.core.length - row.step
  · exact Or.inl hlo
  · by_cases hlast : k = row.core.length - row.step + sources.length
    · exact Or.inr (Or.inr hlast)
    · have hj : k - (row.core.length - row.step) < sources.length := by omega
      obtain ⟨x, hx, he⟩ := native_source_rank_surjective hs hj
      exact Or.inr (Or.inl ⟨x, hx, by omega⟩)

end FullMarkedBLP


