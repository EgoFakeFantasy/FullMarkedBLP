import FullMarkedBLP.NativeFreshCertificate

namespace FullMarkedBLP

theorem nativeFreshValues_eq_getElem {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (owner : RankElementaryEmbedding lambda)
    {a : Pattern} {r k : Nat} {sources : List Nat}
    (hn : nativeSources a r = some sources) (hk : k < sources.length) :
    nativeFreshValues theta owner r sources k =
      (nativeImageColumns theta owner sources)[k]'(by rw [nativeImageColumns_length theta owner hn]; exact hk) := by
  unfold nativeFreshValues
  rw [List.getElem?_eq_getElem (by rw [nativeImageColumns_length theta owner hn]; exact hk)]
  rfl

theorem rankRealization_native_fresh_strict {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r i j : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : nativeSources a r = some sources)
    (hij : i < j) (hj : j < sources.length) :
    nativeFreshValues theta (embedding r) r sources i <
      nativeFreshValues theta (embedding r) r sources j := by
  rw [nativeFreshValues_eq_getElem theta (embedding r) hn (by omega),
    nativeFreshValues_eq_getElem theta (embedding r) hn hj]
  exact List.pairwise_iff_getElem.mp (rankRealization_native_images_sorted h hr hn) i j _ _ hij

theorem rankRealization_native_fresh_lower {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e k : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : nativeSources a r = some sources) (hk : k < sources.length) :
    theta r < nativeFreshValues theta (embedding r) r sources k := by
  rw [nativeFreshValues_eq_getElem theta (embedding r) hn hk]
  exact (rankRealization_native_images_gap h hr hp he hn _ (List.getElem_mem _)).1

end FullMarkedBLP

