import FullMarkedBLP.NativeRankRealization
import FullMarkedBLP.CompletionEarlierMark

namespace FullMarkedBLP

theorem completion_old_rank_certificate {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r y z : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : z ∈ row.marks)
    (hs : sources.Nodup) (hdis : ∀ w ∈ sources, w ∉ row.core)
    (ht : ∀ w, y < w → w ≤ y + sources.length → w ∉ row.core)
    (hcases : ∀ k x, row.step ≤ k → row.core[k]? = some z →
      row.core[k - row.step]? = some x →
      (x ≤ z ∧ z ≤ y ∧ ∀ w ∈ sources, x < w ∧ w < z) ∨
      (x ≤ y ∧ y + sources.length < z ∧ ∀ w ∈ sources, w < x)) :
    ∃ xs delta, MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r z xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  obtain ⟨k, x, xs, delta, hk, hz, hx, htrace, hd, hw⟩ := h.marked r row z hr hm
  refine ⟨xs, delta, ?_, hd, hw⟩
  exact completion_old_markTrace h.valid hr ((h.proper r row hr).2 z hm).1 hm
    hk hz hx htrace hs hdis ht (hcases k x hk hz hx)

end FullMarkedBLP

