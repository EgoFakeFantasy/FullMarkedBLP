import FullMarkedBLP.NativeBlockCertificate

namespace FullMarkedBLP

theorem row_hasRankCertificates_iff {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {ownerEmbedding : RankElementaryEmbedding lambda} {r : Nat} {row : Row}
    (hr : rowAt a r = some row) :
    row.HasRankCertificates a theta embedding ownerEmbedding ↔
    ∀ y ∈ row.marks, ∃ xs delta, MarkTrace a r y xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val ownerEmbedding
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  constructor
  · intro hc y hy
    obtain ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hw⟩ := hc y hy
    exact ⟨xs, delta, ⟨row, k, s, hr, hy, hk, hky, hks, ht⟩, hd, hw⟩
  · intro hc y hy
    obtain ⟨xs, delta, ⟨old, k, s, hold, _, hk, hky, hks, ht⟩, hd, hw⟩ := hc y hy
    have he := Option.some.inj (hold.symm.trans hr)
    subst old
    exact ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hw⟩

theorem rankRealization_native_top_certificates {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) :
    (nativeTop row r sources).HasRankCertificates b
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
      (nativeEmbeddingValues embedding r sources.length) (embedding r) := by
  apply (row_hasRankCertificates_iff (native_top_rowAt hr hn hne)).mpr
  intro y hy
  simp only [nativeTop, mem_canonicalColumns, List.mem_filter] at hy
  rcases List.mem_append.mp hy.1 with hold | hnew
  · obtain ⟨xs, delta, ht, hd, hw⟩ := rankRealization_native_top_old_mark h hr hp he hn hne hold
    rw [nativeEmbeddingValues_block embedding r sources.length sources.length (Nat.le_refl _)] at hw
    exact ⟨xs, delta, ht, hd, hw⟩
  · obtain ⟨j, hj, heq⟩ := List.mem_map.mp hnew
    have hj' := List.mem_range.mp hj
    obtain ⟨p, delta, ht, hd, hw⟩ := rankRealization_native_top_direct_mark h hr hn hj'
    rw [nativeEmbeddingValues_block embedding r sources.length sources.length (Nat.le_refl _)] at hw
    exact ⟨[r + j, p], delta, by simpa only [heq] using ht, hd, hw⟩

end FullMarkedBLP

