import FullMarkedBLP.CompletionOldCertificate

namespace FullMarkedBLP

theorem rankCertificate_set_other {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r owner z : Nat} {old new row : Row}
    (hr : rowAt a r = some old) (hp : new.p = old.p) (ho : owner ≠ r)
    (hrow : rowAt a owner = some row) (hm : z ∈ row.marks) :
    ∃ xs delta, MarkTrace (a.set (r - 1) new) owner z xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (embedding owner)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  obtain ⟨k, s, xs, delta, hk, hz, hs, ht, hd, hw⟩ := h.marked owner row z hrow hm
  exact ⟨xs, delta, (markTrace_set_other_iff hr hp ho).mpr
    ⟨row, k, s, hrow, hm, hk, hz, hs, ht⟩, hd, hw⟩

theorem completion_other_rank_certificate {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r owner y z p : Nat} {old row : Row}
    {sources : List Nat} (hr : rowAt a r = some old) (hp : old.p = some p)
    (ho : owner ≠ r) (hrow : rowAt a owner = some row) (hm : z ∈ row.marks)
    (hs : sources.Nodup) (hdis : ∀ w ∈ sources, w ∉ old.core)
    (ht : ∀ w, y < w → w ≤ y + sources.length → w ∉ old.core)
    (hpy : p ≤ y) (hbelow : ∀ w ∈ sources, w < p) :
    ∃ xs delta, MarkTrace (a.set (r - 1) (completeMarkRow old y sources)) owner z xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (embedding owner)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  exact rankCertificate_set_other h hr
    ((completeMarkRow_p (h.valid r old hr) hp hs hdis ht hpy hbelow).trans hp.symm)
    ho hrow hm

end FullMarkedBLP
