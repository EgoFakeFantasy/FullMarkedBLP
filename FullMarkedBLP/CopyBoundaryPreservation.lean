import FullMarkedBLP.CopyRankRealization

namespace FullMarkedBLP

/-- The copied assignments preserve the first triple and the exact terminal.
The last copied owner is application of the removed owner to the final
literal source owner, numbered e-1. -/
theorem rankRowRealization_shortCopy_boundaries {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {last : Row} {p e : Nat}
    (copy : shortCopy a = some b) (lastAt : rowAt a a.length = some last)
    (hp : last.p = some p) (he : last.e = some e) :
    (∀ i, i ≤ 2 → shortCopyColumnValues theta (embedding a.length) a.length p i = theta i) ∧
    shortCopyColumnValues theta (embedding a.length) a.length p (b.length + 1) = theta (a.length + 1) ∧
    shortCopyEmbeddingValues hl embedding a.length p b.length = rankApply hl (embedding a.length) (embedding (e - 1)) := by
  have valid := h.valid a.length last lastAt
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg (by have := (rowAt_bounds lastAt).1; omega : a.length ≠ 0),
      List.getLast?_eq_getElem?] using lastAt
  have size := (shortCopy_decomposition copy lastGet hp he).1
  have pn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  have pe := row_p_lt_e valid hp he
  have length := shortCopy_length copy lastGet hp he
  have terminalIndex : b.length + 1 = e + (a.length - p) := by omega
  have lastIndex : b.length = (e - 1) + (a.length - p) := by omega
  refine ⟨fun i hi => shortCopyColumnValues_prefix h lastAt hp (by omega), ?_, ?_⟩
  · rw [terminalIndex, shortCopyColumnValues_high theta (embedding a.length) pn pe.le]
    exact realizesEdges_e valid (h.edges a.length last lastAt) he
  · rw [lastIndex]
    exact shortCopyEmbeddingValues_high hl embedding pn (by omega)

/-- A realized nonempty last row has an actual critical point below the
terminal, so application by its owner meets the required bound. -/
theorem rankRowRealization_last_critical {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) (positive : 0 < a.length) :
    ∃ critical, RankCriticalPoint (embedding a.length) critical ∧ critical < theta (a.length + 1) := by
  obtain ⟨last, lastAt⟩ := rowAt_exists positive le_rfl
  have valid := h.valid a.length last lastAt
  have length : 0 < last.core.length := by have := valid.2.1; omega
  let minimum := last.core[0]'length
  have head : last.core.head? = some minimum := by simp [List.head?_eq_getElem?, minimum]
  have bound := core_entry_le_owner valid (List.mem_of_getElem? (show last.core[0]? = some minimum by
    simpa only [List.head?_eq_getElem?] using head))
  exact ⟨theta minimum, h.critical a.length last minimum lastAt head,
    h.increasing minimum (a.length + 1) (by omega) le_rfl⟩

end FullMarkedBLP
