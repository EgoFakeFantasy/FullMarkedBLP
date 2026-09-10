import FullMarkedBLP.NativeHistoricalSuccessor

namespace FullMarkedBLP

theorem native_inserted_edge_from_historical_agreement {lambda delta : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r p e x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (hx : x ∈ sources)
    (other : RankElementaryEmbedding lambda)
    (hc : rankCutoffAgreement delta (embedding r) other)
    (hd : delta ≤ lambda) (hcover : (theta (r + 1)).val ≤ delta) :
    rankOrdinalAction other
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length x) =
    nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length
      (r + 1 + (sources.filter (· < x)).length) := by
  have hk : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have hxr := nativeSources_below_owner h.valid hr hs x hx
  rw [nativeColumnValues_before theta _ hxr.le, nativeColumnValues_inserted theta _ r sources.length _ hk]
  apply rankAgreement_reads_visible_target hc hd
  · exact lt_of_lt_of_le (rankRealization_native_fresh_upper h hr hp he hs _) hcover
  · exact (nativeFreshValues_at_source_rank theta (embedding r) hs hx).symm

end FullMarkedBLP
