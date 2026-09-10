import FullMarkedBLP.ScanFrozenAllCertificates
import FullMarkedBLP.CompletionEventEdges
import FullMarkedBLP.CompletionEventRealization

namespace FullMarkedBLP

/-- Full row realization survives an actual direct intermediate frozen event. -/
theorem scanRankReach_frozen_direct_realization {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (processed : List Nat) (earlier : ∀ z ∈ processed, z < y)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (h : RankRowRealization (processed.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    {row currentRow : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (currentAt : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some currentRow)
    (ht : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some [y, s]) : RankRowRealization
      (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y) theta embedding := by
  have event := scanRankReach_frozen_direct_event_geometry reach entryRealization geometry
    processed earlier events h hr hm currentAt ht
  have certificates := scanRankReach_frozen_direct_all_certificates reach entryRealization geometry
    processed earlier events h hr hm currentAt ht
  obtain ⟨phi, _, _, _, certs⟩ := scanRankReach_current_historical_certificates reach entryRealization geometry hr
  obtain ⟨xs, delta, oldTrace, _, _, _⟩ := certs y hm
  obtain ⟨current, _, _, hcAt, currentMark, _⟩ := frozen_fold_preserves_historical_trace processed events oldTrace
  have eq := Option.some.inj (hcAt.symm.trans currentAt)
  subst current
  have entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i := by
    intro before history owner prior bound
    obtain ⟨oldTheta, oldEmbedding, lifted⟩ := scanReach_rank_lift prior initialTheta initialEmbedding
    exact (geometry before history owner oldTheta oldEmbedding lifted bound).1
  have edges := completionEvent_frozen_prefix_all_edges entrances
    (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) processed event currentAt currentMark
  exact completionEvent_realization event currentAt currentMark edges certificates

end FullMarkedBLP
