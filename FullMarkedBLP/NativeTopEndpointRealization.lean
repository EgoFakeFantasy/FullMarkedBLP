import FullMarkedBLP.NativeOldEdgeIntervals

namespace FullMarkedBLP

/-- The top e edge retains the old endpoint value at its shifted implicit
column. This proves the endpoint case without assuming top realization. -/
theorem rankRealization_native_top_endpoint {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) :
    (nativeTop row r sources).e = some e ∧
    rankOrdinalAction (nativeEmbeddingValues embedding r sources.length (r + sources.length))
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length e) =
    nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length
      (r + sources.length + 1) := by
  refine ⟨nativeTop_e h.valid hr hp he hs, ?_⟩
  have hv := h.valid r row hr
  have her := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
  have hshift : r + sources.length + 1 = shiftAfter r sources.length (r + 1) := by
    unfold shiftAfter
    rw [if_pos (by omega)]
    omega
  rw [nativeEmbeddingValues_block embedding r sources.length sources.length (Nat.le_refl _),
    nativeColumnValues_before theta _ her, hshift, nativeColumnValues_preserves]
  exact realizesEdges_e hv (h.edges r row hr) he

end FullMarkedBLP

