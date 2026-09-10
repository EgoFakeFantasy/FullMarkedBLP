import FullMarkedBLP.NativeRankRealization

namespace FullMarkedBLP

theorem rankMarkedRealization_native {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) {r : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) :
    RankMarkedRealization b
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
      (nativeEmbeddingValues embedding r sources.length) := by
  exact rankRowRealization_with_sat
    (rankRowRealization_native hl (rankMarkedRealization_toRows h) hn)
    (native_sat_of_others h.valid (fun i row _ hr => h.sat i row hr) hn)

end FullMarkedBLP
