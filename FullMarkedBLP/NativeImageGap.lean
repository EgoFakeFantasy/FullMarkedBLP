import FullMarkedBLP.NativeColumnValues

namespace FullMarkedBLP

/-- Images of the actual native sources lie strictly inside the insertion gap. -/
theorem rankRealization_native_source_image_gap {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : nativeSources a r = some sources) (hx : x ∈ sources) :
    theta r < rankOrdinalAction (embedding r) (theta x) ∧
      rankOrdinalAction (embedding r) (theta x) < theta (r + 1) := by
  have hb := nativeSources_between h.valid hr hp he hn x hx
  have hv := h.valid r row hr
  have hrb := (rowAt_bounds hr).2
  have heb := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
  have hl := rankOrdinalAction_strictMono (embedding r)
    (h.increasing p x hb.1 (by omega))
  have hu := rankOrdinalAction_strictMono (embedding r)
    (h.increasing x e hb.2 (by omega))
  have hpi := realizesEdges_p hv (h.edges r row hr) hp
  have hei := realizesEdges_e hv (h.edges r row hr) he
  exact ⟨by simpa only [hpi] using hl, by simpa only [hei] using hu⟩

end FullMarkedBLP

