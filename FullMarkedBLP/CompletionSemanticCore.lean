import FullMarkedBLP.CompletionPacketGeometry

namespace FullMarkedBLP

/-- Actual packet edges inside one old target gap derive both source
disjointness and p preservation, as well as the completed core's validity. -/
theorem rankRealization_completion_core_and_p {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r k y p nextTarget : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (hs : sources.Nodup) (bounds : ∀ x ∈ sources, x ≤ a.length + 1)
    (gap : y + sources.length < nextTarget) (beforeOwner : y + sources.length < r)
    (packet : ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length)) :
    (completeMarkRow row y sources).CoreValid r ∧ (completeMarkRow row y sources).p = some p := by
  obtain ⟨left, right, hl, hrr, sourceGap, hdis, targetGap, below, hpy⟩ :=
    rankRealization_completion_geometry h hr hp hk hy hnt bounds gap beforeOwner packet
  have hv := h.valid r row hr
  exact ⟨completeMarkRow_coreValid hv hs hdis (fun x hx => (below x hx).le.trans hpy)
      targetGap (by omega),
    completeMarkRow_p hv hp hs hdis targetGap hpy below⟩

end FullMarkedBLP
