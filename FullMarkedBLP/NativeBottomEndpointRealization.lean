import FullMarkedBLP.NativeInsertedPairs

namespace FullMarkedBLP

/-- The actual bottom native row has both p-to-owner and e-to-successor edges realized by the
retained owner, with the first inserted column obtained from the least source. -/
theorem rankRealization_native_bottom_endpoint {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e last : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : native a r = some (b, sources)) (hlast : sources.getLast? = some last)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda) :
    ∃ bottom, rowAt b r = some bottom ∧ bottom.p = some p ∧ bottom.e = some last ∧
      rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length r)
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length p) =
      nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length r ∧
      rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length r)
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length last) =
      nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length (r + 1) := by
  have hs := native_sources_of_success hn
  obtain ⟨bottom, er, v, hb, hbp, hbe, _, _, _⟩ := native_bottom_sat_witness h.valid hr hp he hs hlast hn
  have hmin := decreasing_last_min (nativeSources_decreasing h.valid hs) hlast
  have hf : sources.filter (· < last) = [] := List.filter_eq_nil_iff.mpr
    (fun x hx => by have hh := hmin x hx; simp; omega)
  refine ⟨bottom, hb, hbp, hbe, ?_, ?_⟩
  · have hv := h.valid r row hr
    have hpr : p ≤ r := fromRight_le_last hv.1 hv.2.2.1 (by omega : 0 < row.step + 1) hp
    rw [nativeColumnValues_before embedding freshEmbedding (Nat.le_refl r),
      nativeColumnValues_before theta _ hpr,
      nativeColumnValues_before theta _ (Nat.le_refl r)]
    exact realizesEdges_p hv (h.edges r row hr) hp
  · simpa only [hf, List.length_nil, Nat.add_zero] using
      rankRealization_native_inserted_pair h hr hs (List.mem_of_getLast? hlast) freshEmbedding
end FullMarkedBLP



