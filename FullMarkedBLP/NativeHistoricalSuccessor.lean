import FullMarkedBLP.NativeHistoricalCoverage

namespace FullMarkedBLP

theorem native_successor_stays_below_historical_cutoff {lambda delta : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r p e v : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (hd : (theta (v + 1)).val ≤ delta) :
    (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length
      (shiftAfter r sources.length v + 1)).val ≤ delta := by
  have hb := nativeColumnValues_successor_le theta
    (nativeFreshValues theta (embedding r) r sources) r sources.length v
    (fun _ => (rankRealization_native_fresh_upper h hr hp he hs 0).le)
  exact le_trans hb hd

end FullMarkedBLP
