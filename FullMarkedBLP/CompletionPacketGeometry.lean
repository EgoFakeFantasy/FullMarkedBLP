import FullMarkedBLP.CompletionSemanticPosition
import FullMarkedBLP.NativePrefixEdges

namespace FullMarkedBLP

/-- Shared geometric consequences of actual packet edges in one old target gap. -/
theorem rankRealization_completion_geometry {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r k y p nextTarget : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (bounds : ∀ x ∈ sources, x ≤ a.length + 1)
    (gap : y + sources.length < nextTarget) (beforeOwner : y + sources.length < r)
    (packet : ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length)) :
    ∃ left right, row.core[k - row.step]? = some left ∧
      row.core[k - row.step + 1]? = some right ∧
      (∀ x ∈ sources, left < x ∧ x < right) ∧
      (∀ x ∈ sources, x ∉ row.core) ∧
      (∀ z, y < z → z ≤ y + sources.length → z ∉ row.core) ∧
      (∀ x ∈ sources, x < p) ∧ p ≤ y := by
  have hv := h.valid r row hr
  have hrowBound := (rowAt_bounds hr).2
  have hnext := full_entry_le_endpoint hv hnt
  have hki := (List.getElem?_eq_some_iff.mp hy).1
  have hstep := hv.2.2.2.1
  have hleftBound : k - row.step < row.core.length := by omega
  have hrightBound : k - row.step + 1 < row.core.length := by omega
  let left := row.core[k - row.step]
  let right := row.core[k - row.step + 1]
  have hl : row.core[k - row.step]? = some left := by simp [left, hleftBound]
  have hrr : row.core[k - row.step + 1]? = some right := by simp [right, hrightBound]
  have sourceGap : ∀ x ∈ sources, left < x ∧ x < right := by
    intro x hx
    have hi : (sources.filter (· < x)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
    exact rankRealization_source_gap h hr hk hl hrr hy hnt (bounds x hx)
      (by omega) (by omega) (by omega) (by omega) (packet x hx)
  have hdis : ∀ x ∈ sources, x ∉ row.core := by
    intro x hx
    exact between_adjacent_not_mem hv.1 hl hrr (sourceGap x hx).1 (sourceGap x hx).2
  have targetGap : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core := by
    intro z hz hzb hmem
    have hnot := between_adjacent_not_mem (coreValid_full_sorted hv)
      (full_entry_of_core hy) hnt hz (by omega : z < nextTarget)
    exact hnot (List.mem_append_left _ hmem)
  have below : ∀ x ∈ sources, x < p := by
    intro x hx
    have hi : (sources.filter (· < x)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
    exact rankRealization_edge_source_below_p h hr hp (bounds x hx) (by omega) (packet x hx)
  have hpy := target_position_after_p hv hk hy hp
  exact ⟨left, right, hl, hrr, sourceGap, hdis, targetGap, below, hpy⟩

end FullMarkedBLP

