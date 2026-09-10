import FullMarkedBLP.CompletionTargetBound

namespace FullMarkedBLP

theorem rankRealization_column_lt_iff {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {i j : Nat}
    (hi : i ≤ a.length + 1) (hj : j ≤ a.length + 1) : theta i < theta j ↔ i < j := by
  constructor
  · intro hlt
    by_contra hn
    rcases eq_or_lt_of_le (Nat.le_of_not_gt hn) with he | he
    · exact (lt_irrefl (theta i)) (by simpa only [he] using hlt)
    · exact (not_lt_of_ge (h.increasing j i he hi).le) hlt
  · intro hij
    exact h.increasing i j hij hj

/-- An actual image in a target gap forces its source into the corresponding
    source gap. Both bounding edges are read from the literal full row. -/
theorem rankRealization_source_gap {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r k left right y nextTarget x z : Nat} {row : Row}
    (hr : rowAt a r = some row) (hk : row.step ≤ k)
    (hl : row.core[k - row.step]? = some left)
    (hrr : row.core[k - row.step + 1]? = some right)
    (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (hx : x ≤ a.length + 1) (hz : z ≤ a.length + 1)
    (hnext : nextTarget ≤ a.length + 1)
    (hyz : y < z) (hzn : z < nextTarget)
    (himage : rankOrdinalAction (embedding r) (theta x) = theta z) : left < x ∧ x < right := by
  have hv := h.valid r row hr
  have howner := (rowAt_bounds hr).2
  have hleft := core_entry_le_owner hv (List.mem_of_getElem? hl)
  have hright := core_entry_le_owner hv (List.mem_of_getElem? hrr)
  have hyowner := core_entry_le_owner hv (List.mem_of_getElem? hy)
  have hil : k - row.step + row.step = k := by omega
  have hir : k - row.step + 1 + row.step = k + 1 := by omega
  have hleftImage := h.edges r row hr (k - row.step) left y (full_entry_of_core hl)
    (by simpa only [hil] using (full_entry_of_core (owner := r) hy))
  have hrightImage := h.edges r row hr (k - row.step + 1) right nextTarget (full_entry_of_core hrr)
    (by simpa only [hir] using hnt)
  have hlow : theta left < theta x := (rankOrdinalAction_lt_iff (embedding r) _ _).mp (by
    rw [hleftImage, himage]
    exact h.increasing y z hyz hz)
  have hhigh : theta x < theta right := (rankOrdinalAction_lt_iff (embedding r) _ _).mp (by
    rw [himage, hrightImage]
    exact h.increasing z nextTarget hzn hnext)
  exact ⟨(rankRealization_column_lt_iff h (by omega) hx).mp hlow,
    (rankRealization_column_lt_iff h hx (by omega)).mp hhigh⟩

theorem rankRealization_source_gap_not_mem {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r i left right x : Nat} {row : Row}
    (hr : rowAt a r = some row) (hl : row.core[i]? = some left)
    (hrr : row.core[i + 1]? = some right) (hx : left < x ∧ x < right) : x ∉ row.core :=
  between_adjacent_not_mem (h.valid r row hr).1 hl hrr hx.1 hx.2

end FullMarkedBLP


