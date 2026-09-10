import FullMarkedBLP.RankCardinalPreservation

namespace FullMarkedBLP

theorem rankRowRealization_native {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) :
    RankRowRealization b
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
      (nativeEmbeddingValues embedding r sources.length) := by
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  have hv := h.valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
  refine ⟨native_preserves_coreValid h.valid hn, native_preserves_properMarks h.valid h.proper hn,
    ?_,
    rankRealization_native_all_cardinals hl h hn, rankRealization_native_all_edges h hn,
    rankRealization_native_all_critical h hn, ?_⟩
  · intro i j hij hj
    have hlen := native_length hn
    exact rankRealization_native_columns_strict h hr hp he (native_sources_of_success hn) hij (by omega)
  · intro i row y hr hy
    exact rankRealization_native_all_certificates h hn i row hr y hy

end FullMarkedBLP


