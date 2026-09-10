import FullMarkedBLP.ScanDirectEndpointAgreement
import FullMarkedBLP.ScanDirectOwnerEdges

namespace FullMarkedBLP

/-- The actual direct entrance packet follows from birth edges and historical
agreement; only increasing current columns are needed, not current realization. -/
theorem scanRankReach_direct_owner_packet {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j)
    {row : Row} {sources : List Nat} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (ht : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources) :
    ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length) := by
  have saved := scanRankReach_direct_endpoint_agreement reach entryRealization geometry hr hm ht hc
  have edges := scanRankReach_completion_direct_edges reach
    (fun before history owner oldTheta oldEmbedding prior bound =>
      (geometry before history owner oldTheta oldEmbedding prior bound).1) ht hc
  have record := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  have bound := scanReach_record_targets_before (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) record
  have rb := rowAt_bounds hr
  intro x hx
  have rank : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have visible := increasing (y + ((sources.filter (· < x)).length + 1))
    (y + sources.length + 1) (by omega) (by omega)
  have transferred := rankAgreement_reads_visible_target
    (fun u v hu hv => (saved u v hu hv).symm) (theta (y + sources.length + 1)).property.le
    visible (edges x hx)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using transferred

end FullMarkedBLP
