import FullMarkedBLP.CopyHighCertificates
import FullMarkedBLP.CopyLowCertificates
import FullMarkedBLP.CopyMiddleCertificates
import FullMarkedBLP.CopyPrefixCertificates

namespace FullMarkedBLP

/-- All three actual retention branches have their full natural certificates. -/
theorem copiedRow_all_marked {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last row copied : Row} {p e source : Nat}
    (copy : shortCopy a = some b) (lastAt : rowAt a a.length = some last)
    (hp : last.p = some p) (he : last.e = some e) (hps : p ≤ source) (hse : source ≤ e)
    (sourceAt : rowAt a source = some row) (rowCopy : copiedRow a last source row = some copied)
    (copiedAt : rowAt b (source + (a.length - p)) = some copied) :
    ∀ x ∈ copied.marks, ∃ k s word delta, copied.step ≤ k ∧ copied.core[k]? = some x ∧
      copied.core[k - copied.step]? = some s ∧ Trace b s x word ∧
      naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
        (shortCopyColumnValues theta (embedding a.length) a.length p) word.dropLast = some delta ∧
      rankCutoffAgreement delta.val
        (shortCopyEmbeddingValues hl embedding a.length p (source + (a.length - p)))
        (evalWord (fun i => (shortCopyEmbeddingValues hl embedding a.length p i :
          RankDomain lambda → RankDomain lambda)) word.dropLast) := by
  have hn : a.length ≠ 0 := Nat.ne_of_gt (rowAt_bounds lastAt).1
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg hn, List.getLast?_eq_getElem?] using lastAt
  intro x newMark
  obtain ⟨index, y, mark, markAtOld, markAtCopy, targetMap, allowed⟩ := copiedRow_mark_origin rowCopy newMark
  obtain ⟨last', minimum, p', xs, terminal, lastGet', minimumAt, hp', computed, terminalAt, cases⟩ :=
    copyMarkAllowed_cases allowed
  have sameLast := Option.some.inj (lastGet'.symm.trans lastGet)
  subst last'
  have sameP := Option.some.inj (hp'.symm.trans hp)
  subst p'
  rcases cases with high | ⟨terminalLow, low, firstLow, cases⟩
  · exact copiedRow_high_marked hl h copy lastAt hp he hps hse sourceAt rowCopy mark targetMap computed terminalAt high
  · rcases cases with lowBelow | ⟨lowAbove, bridgeIndex, shifted, findIndex, shiftedAt, bridgeMark, guard⟩
    · exact copiedRow_low_marked hl h copy lastAt hp he hps hse minimumAt lowBelow
        sourceAt rowCopy mark targetMap computed terminalAt terminalLow firstLow
    · obtain ⟨indexBound, indexValue, _⟩ := List.findIdx?_eq_some_iff_getElem.mp findIndex
      have lowAt : last.core[bridgeIndex]? = some low :=
        List.getElem?_eq_some_iff.mpr ⟨indexBound, by simpa using indexValue⟩
      exact copiedRow_middle_marked hl h copy lastAt hp he hps hse minimumAt lowAbove
        sourceAt rowCopy copiedAt mark newMark markAtOld markAtCopy targetMap computed firstLow
        lowAt shiftedAt bridgeMark guard

theorem shortCopy_all_marked {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p e : Nat} (copy : shortCopy a = some b)
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p) (he : last.e = some e) :
    ∀ r row y, rowAt b r = some row → y ∈ row.marks →
      ∃ k s word delta, row.step ≤ k ∧ row.core[k]? = some y ∧ row.core[k - row.step]? = some s ∧
        Trace b s y word ∧
        naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
          (shortCopyColumnValues theta (embedding a.length) a.length p) word.dropLast = some delta ∧
        rankCutoffAgreement delta.val (shortCopyEmbeddingValues hl embedding a.length p r)
          (evalWord (fun i => (shortCopyEmbeddingValues hl embedding a.length p i :
            RankDomain lambda → RankDomain lambda)) word.dropLast) := by
  have hn : a.length ≠ 0 := Nat.ne_of_gt (rowAt_bounds lastAt).1
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg hn, List.getLast?_eq_getElem?] using lastAt
  have valid := h.valid a.length last lastAt
  have hpn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  intro r row y rowAtCopy mark
  by_cases before : r < a.length
  · exact shortCopy_prefix_marked hl h copy lastAt hp before rowAtCopy mark
  · obtain ⟨source, old, sourceGe, sourceLt, targetEq, sourceAt, rowCopy⟩ :=
      shortCopy_row_origin copy lastGet hp he hpn (by omega) rowAtCopy
    subst r
    exact copiedRow_all_marked hl h copy lastAt hp he sourceGe sourceLt.le sourceAt rowCopy rowAtCopy y mark

end FullMarkedBLP
