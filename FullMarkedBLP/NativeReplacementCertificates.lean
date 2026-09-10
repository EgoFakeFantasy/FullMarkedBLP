import FullMarkedBLP.NativeActualBlockCertificates

namespace FullMarkedBLP

theorem rankRealization_native_replacement_certificates {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : native a r = some (b, sources)) (hne : sources ≠ [])
    {i : Nat} {target : Row} (hi : r ≤ i) (hi' : i ≤ r + sources.length)
    (ht : rowAt b i = some target) :
    target.HasRankCertificates b
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
      (nativeEmbeddingValues embedding r sources.length)
      (nativeEmbeddingValues embedding r sources.length i) := by
  have hn' := hn
  unfold native at hn'
  rw [hr] at hn'
  dsimp only [Bind.bind, Option.bind] at hn'
  obtain ⟨ss, hs, hn'⟩ := Option.bind_eq_some_iff.mp hn'
  obtain ⟨block, hb, hn'⟩ := Option.bind_eq_some_iff.mp hn'
  change some (_, ss) = some (b, sources) at hn'
  cases Option.some.inj hn'
  obtain ⟨actual, ha, hac⟩ := rankRealization_native_actual_block_certificates h hr hp he hn hne
  have heq := Option.some.inj (hb.symm.trans ha)
  subst actual
  have hl := nativeBlock_length hb
  have hj : i - r < block.length := by omega
  have hiEq : i = r + (i - r) := by omega
  have ht' := ht
  rw [hiEq, native_block_rowAt hr hj] at ht'
  obtain ⟨hidx, hv⟩ := List.getElem?_eq_some_iff.mp ht'
  have hc := hac (i - r) hidx
  rw [hv] at hc
  have hei : nativeEmbeddingValues embedding r sources.length i = embedding r := by
    rw [hiEq]
    exact nativeEmbeddingValues_block embedding r sources.length (i - r) (by omega)
  rw [hei]
  exact hc

end FullMarkedBLP

