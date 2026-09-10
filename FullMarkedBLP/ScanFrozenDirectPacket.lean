import FullMarkedBLP.ScanFrozenDirectEndpoint
import FullMarkedBLP.ScanDirectOwnerEdges

namespace FullMarkedBLP

/-- Intermediate direct packet edges follow from record birth edges and the transported endpoint agreement. -/
theorem scanRankReach_frozen_direct_owner_packet {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row currentRow : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (currentRowAt : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some currentRow)
    (sorted : currentRow.core.Pairwise (· < ·))
    (ht : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some [y, s])
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length) := by
  have saved := scanRankReach_frozen_direct_endpoint_agreement reach entryRealization geometry
    processed events hr hm currentRowAt sorted ht hc
  have record := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  have sourceBounds := scanRankReach_record_source_bounds reach
    (fun before history owner oldTheta oldEmbedding prior bound =>
      (geometry before history owner oldTheta oldEmbedding prior bound).1) record
  have bound := scanReach_record_targets_before (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) record
  have rb := rowAt_bounds hr
  intro x hx
  have edge := scanRankReach_record_edges reach record
    (fun x hx => Nat.le_of_lt (sourceBounds x hx)) x hx
  have rank : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have visible := increasing (y + 1 + (sources.filter (· < x)).length)
    (y + sources.length + 1) (by omega) (by omega)
  exact rankAgreement_reads_visible_target
    (fun u v hu hv => (saved u v hu hv).symm) (theta (y + sources.length + 1)).property.le
    visible edge

end FullMarkedBLP
