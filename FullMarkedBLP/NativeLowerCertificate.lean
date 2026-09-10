import FullMarkedBLP.NativeTopOldCertificate

namespace FullMarkedBLP

/-- Natural marked certificates of a literal row in a fixed ambient output.
Keeping the row embedding explicit allows descent through a repeated-owner block. -/
def Row.HasRankCertificates {lambda : Ordinal.{u}} (a : Pattern)
    (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda)
    (ownerEmbedding : RankElementaryEmbedding lambda) (row : Row) : Prop :=
  ∀ y ∈ row.marks, ∃ k s xs delta, row.step ≤ k ∧ row.core[k]? = some y ∧
    row.core[k - row.step]? = some s ∧ Trace a s y xs ∧
    naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
    rankCutoffAgreement delta.val ownerEmbedding
      (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast)

theorem nativeLower_medium_rankCertificates {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {ownerEmbedding : RankElementaryEmbedding lambda} {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (hc : row.HasRankCertificates a theta embedding ownerEmbedding)
    (hl : nativeLower row owner true = some lower) :
    lower.HasRankCertificates a theta embedding ownerEmbedding := by
  intro y hy
  have hy' := (nativeLower_marks_sublist hl).subset hy
  obtain ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hw⟩ := hc y hy'
  have hp := nativeLower_medium_pair hv (hm.2 y hy').1 hky hks hl
  have hs := nativeLower_step hl
  simp only [↓reduceIte] at hs
  exact ⟨k, s, xs, delta, by omega, hp.1, hp.2, ht, hd, hw⟩

theorem nativeLower_short_rankCertificates {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {ownerEmbedding : RankElementaryEmbedding lambda} {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (hlen : row.core.length + 1 = 2 * row.step)
    (hc : row.HasRankCertificates a theta embedding ownerEmbedding)
    (hl : nativeLower row owner false = some lower) :
    lower.HasRankCertificates a theta embedding ownerEmbedding := by
  intro y hy
  have hy' := (nativeLower_marks_sublist hl).subset hy
  obtain ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hw⟩ := hc y hy'
  have hp := nativeLower_short_pair hv hm hlen hy' hk hky hks hl
  have hs := nativeLower_step hl
  simp only [Bool.false_eq_true, ↓reduceIte] at hs
  exact ⟨k - 1, s, xs, delta, by omega, hp.1, hp.2, ht, hd, hw⟩

end FullMarkedBLP
