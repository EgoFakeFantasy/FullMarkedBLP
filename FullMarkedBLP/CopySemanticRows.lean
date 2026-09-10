import FullMarkedBLP.CopySemanticEdges
import FullMarkedBLP.CopyDecomposition

namespace FullMarkedBLP

theorem shortCopy_realizes_all_edges {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p e : Nat} (copy : shortCopy a = some b)
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p) (he : last.e = some e) :
    ∀ r row, rowAt b r = some row → row.RealizesEdges
      (rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p r))
      (shortCopyColumnValues theta (embedding a.length) a.length p) r := by
  have hn : a.length ≠ 0 := Nat.ne_of_gt (rowAt_bounds lastAt).1
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg hn, List.getLast?_eq_getElem?] using lastAt
  have valid := h.valid a.length last lastAt
  have hpn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  intro r row rowAtCopy
  by_cases before : r < a.length
  · have rowAtOld := (shortCopy_prefix_rowAt copy before).symm.trans rowAtCopy
    rw [shortCopyEmbeddingValues, if_pos before]
    intro k x y hx hy
    have hxb := full_entry_le_endpoint (h.valid r row rowAtOld) hx
    have hyb := full_entry_le_endpoint (h.valid r row rowAtOld) hy
    rw [shortCopyColumnValues_prefix h lastAt hp (by omega : x ≤ a.length),
      shortCopyColumnValues_prefix h lastAt hp (by omega : y ≤ a.length)]
    exact h.edges r row rowAtOld k x y hx hy
  · obtain ⟨source, old, sourceGe, _, targetEq, sourceAt, copiedEq⟩ :=
      shortCopy_row_origin copy lastGet hp he hpn (by omega) rowAtCopy
    rw [targetEq, shortCopyEmbeddingValues_high hl embedding hpn sourceGe]
    exact copiedRow_realizesEdges hl h lastAt hp sourceAt sourceGe copiedEq

theorem shortCopy_realizes_all_criticalPoints {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p e : Nat} (copy : shortCopy a = some b)
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p) (he : last.e = some e) :
    ∀ r row minimum, rowAt b r = some row → row.core.head? = some minimum →
      RankCriticalPoint (shortCopyEmbeddingValues hl embedding a.length p r)
        (shortCopyColumnValues theta (embedding a.length) a.length p minimum) := by
  have hn : a.length ≠ 0 := Nat.ne_of_gt (rowAt_bounds lastAt).1
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg hn, List.getLast?_eq_getElem?] using lastAt
  have valid := h.valid a.length last lastAt
  have hpn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  intro r row minimum rowAtCopy minimumAt
  by_cases before : r < a.length
  · have rowAtOld := (shortCopy_prefix_rowAt copy before).symm.trans rowAtCopy
    have minimumEntry : row.core[0]? = some minimum := by
      simpa only [List.head?_eq_getElem?] using minimumAt
    have minimumBound := core_entry_le_owner (h.valid r row rowAtOld) (List.mem_of_getElem? minimumEntry)
    rw [shortCopyEmbeddingValues, if_pos before,
      shortCopyColumnValues_prefix h lastAt hp (by omega : minimum ≤ a.length)]
    exact h.critical r row minimum rowAtOld minimumAt
  · obtain ⟨source, old, sourceGe, _, targetEq, sourceAt, copiedEq⟩ :=
      shortCopy_row_origin copy lastGet hp he hpn (by omega) rowAtCopy
    rw [targetEq, shortCopyEmbeddingValues_high hl embedding hpn sourceGe]
    exact copiedRow_criticalPoint hl h lastAt hp sourceAt copiedEq minimumAt

end FullMarkedBLP
