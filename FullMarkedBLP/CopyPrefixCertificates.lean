import FullMarkedBLP.CopyWordCertificates
import FullMarkedBLP.CopyRowTraces

namespace FullMarkedBLP

theorem shortCopy_prefix_marked {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last row : Row} {p r y : Nat} (copy : shortCopy a = some b)
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p)
    (before : r < a.length) (rowAtCopy : rowAt b r = some row) (mark : y ∈ row.marks) :
    ∃ k s xs delta, row.step ≤ k ∧ row.core[k]? = some y ∧ row.core[k - row.step]? = some s ∧
      Trace b s y xs ∧
      naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
        (shortCopyColumnValues theta (embedding a.length) a.length p) xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (shortCopyEmbeddingValues hl embedding a.length p r)
        (evalWord (fun i => (shortCopyEmbeddingValues hl embedding a.length p i :
          RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  have rowAtOld := (shortCopy_prefix_rowAt copy before).symm.trans rowAtCopy
  obtain ⟨k, s, xs, delta, stepBound, markAt, sourceAt, trace, cutoff, certificate⟩ :=
    h.marked r row y rowAtOld mark
  have yr := (h.proper r row rowAtOld).2 y mark
  have bounded : ∀ v ∈ xs.dropLast, v < a.length := by
    intro v hv
    have vy := trace_member_le_head h.valid trace (List.mem_of_mem_dropLast hv)
    omega
  obtain ⟨newCutoff, newCertificate⟩ :=
    shortCopy_prefix_natural_certificate hl h lastAt hp before xs.dropLast bounded cutoff certificate
  exact ⟨k, s, xs, delta, stepBound, markAt, sourceAt,
    shortCopy_prefix_trace h.valid copy trace (by omega), newCutoff, newCertificate⟩

end FullMarkedBLP
