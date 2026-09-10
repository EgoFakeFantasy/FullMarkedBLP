import FullMarkedBLP.NativeHistoricalAgreement

namespace FullMarkedBLP

theorem native_inserted_targets_below_historical_cutoff {lambda delta : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (hd : (theta (r + 1)).val ≤ delta) :
    ∀ k, k < sources.length →
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length
        (r + 1 + k)).val < delta := by
  intro k hk
  rw [nativeColumnValues_inserted theta _ r sources.length k hk]
  exact lt_of_lt_of_le (rankRealization_native_fresh_upper h hr hp he hs k) hd

theorem native_old_target_stays_covered {lambda delta : Ordinal.{u}}
    (theta fresh : Nat → OrdinalDomain lambda) (r t x : Nat)
    (hx : (theta x).val < delta) :
    (nativeColumnValues theta fresh r t (shiftAfter r t x)).val < delta := by
  rwa [nativeColumnValues_preserves]

end FullMarkedBLP
