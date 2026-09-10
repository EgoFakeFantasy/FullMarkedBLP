import FullMarkedBLP.CopyFrozenAllCertificates

namespace FullMarkedBLP

/-- Full row realization survives an arbitrary-word frozen event after a Sat short copy. -/
theorem shortCopy_frozen_realization {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    (processed : List Nat) (earlier : ∀ z ∈ processed, z < y)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (h : RankRowRealization (processed.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    {row currentRow : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (currentAt : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some currentRow) : RankRowRealization
      (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y) theta embedding := by
  have geometry := scanPriorVerifiedEvents_geometry verified
  have event := shortCopy_frozen_event_geometry parentValid sat copy reach entryRealization currentReal verified
    processed earlier events h hr hm currentAt
  have certificates := shortCopy_frozen_all_certificates parentValid sat copy reach entryRealization currentReal verified
    processed earlier events h hr hm currentAt
  obtain ⟨phi, _, _, _, certs⟩ := scanRankReach_current_historical_certificates reach entryRealization geometry hr
  obtain ⟨xs, delta, oldTrace, _, _, _⟩ := certs y hm
  obtain ⟨current, _, _, hcAt, currentMark, _⟩ := frozen_fold_preserves_historical_trace processed events oldTrace
  have eq := Option.some.inj (hcAt.symm.trans currentAt)
  subst current
  have entrances : ∀ before history owner, ScanReach copied before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i := by
    intro before history owner prior bound
    obtain ⟨oldTheta, oldEmbedding, lifted⟩ := scanReach_rank_lift prior initialTheta initialEmbedding
    exact (geometry before history owner oldTheta oldEmbedding lifted bound).1
  have edges := completionEvent_frozen_prefix_all_edges entrances
    (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) processed event currentAt currentMark
  exact completionEvent_realization event currentAt currentMark edges certificates

end FullMarkedBLP
