import FullMarkedBLP.NativePrefixCritical

namespace FullMarkedBLP

theorem nativeFreshValues_at_source_rank {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (owner : RankElementaryEmbedding lambda)
    {a : Pattern} {r x : Nat} {sources : List Nat}
    (hn : nativeSources a r = some sources) (hx : x ∈ sources) :
    nativeFreshValues theta owner r sources (sources.filter (· < x)).length =
      rankOrdinalAction owner (theta x) := by
  have hi := sorted_get_at_rank (canonicalColumns_sorted sources)
    ((mem_canonicalColumns x sources).mpr hx)
  rw [canonical_filter_length (nativeSources_nodup_of_success hn)] at hi
  unfold nativeFreshValues nativeImageColumns
  rw [List.getElem?_map, hi]
  rfl

/-- Each actual source paired with its insertion-rank target is realized by
    the retained owner embedding in the concrete new column interpretation. -/
theorem rankRealization_native_inserted_pair {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : nativeSources a r = some sources) (hx : x ∈ sources)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda) :
    rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length r)
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length x) =
    nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length
      (r + 1 + (sources.filter (· < x)).length) := by
  have hxr := nativeSources_below_owner h.valid hr hn x hx
  have hi := sorted_get_at_rank (canonicalColumns_sorted sources)
    ((mem_canonicalColumns x sources).mpr hx)
  rw [canonical_filter_length (nativeSources_nodup_of_success hn)] at hi
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  rw [canonicalColumns_length (nativeSources_nodup_of_success hn)] at hib
  rw [nativeColumnValues_before embedding freshEmbedding (Nat.le_refl r),
    nativeColumnValues_before theta _ hxr.le,
    nativeColumnValues_inserted theta _ r sources.length _ hib,
    nativeFreshValues_at_source_rank theta (embedding r) hn hx]

end FullMarkedBLP

