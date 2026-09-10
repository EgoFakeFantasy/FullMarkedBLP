import FullMarkedBLP.NativeImageGap

namespace FullMarkedBLP

noncomputable def nativeImageColumns {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (owner : RankElementaryEmbedding lambda)
    (sources : List Nat) : List (OrdinalDomain lambda) :=
  (canonicalColumns sources).map (fun x => rankOrdinalAction owner (theta x))

theorem nativeImageColumns_length {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (owner : RankElementaryEmbedding lambda)
    {a : Pattern} {r : Nat} {sources : List Nat} (hn : nativeSources a r = some sources) :
    (nativeImageColumns theta owner sources).length = sources.length := by
  rw [nativeImageColumns, List.length_map,
    canonicalColumns_length (nativeSources_nodup_of_success hn)]

theorem rankRealization_native_images_sorted {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : nativeSources a r = some sources) :
    (nativeImageColumns theta (embedding r) sources).Pairwise (· < ·) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := canonicalColumns_sorted sources)
  intro x y hx hy hxy
  have hyb := nativeSources_below_owner h.valid hr hn y ((mem_canonicalColumns y sources).mp hy)
  have hrb := (rowAt_bounds hr).2
  exact rankOrdinalAction_strictMono (embedding r) (h.increasing x y hxy (by omega))

theorem rankRealization_native_images_gap {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : nativeSources a r = some sources) :
    ∀ value ∈ nativeImageColumns theta (embedding r) sources,
      theta r < value ∧ value < theta (r + 1) := by
  intro value hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
  exact rankRealization_native_source_image_gap h hr hp he hn
    ((mem_canonicalColumns x sources).mp hx)

end FullMarkedBLP

