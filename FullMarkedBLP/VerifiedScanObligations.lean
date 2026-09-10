import FullMarkedBLP.ScanOriginalBIntervals

namespace FullMarkedBLP

/-- The earlier verified events discharge the auxiliary geometric obligation. -/
theorem scanPriorVerifiedEvents_geometry {lambda : Ordinal.{u}} {initial : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {r : Nat}
    (verified : ScanPriorVerifiedEvents initial initialTheta initialEmbedding r) :
    ScanPriorGeometry initial initialTheta initialEmbedding r := by
  intro before history owner theta embedding reach earlier
  obtain ⟨h, events⟩ := verified before history owner theta embedding reach earlier
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  by_cases bound : owner ≤ before.length
  · have positive := (scanReach_records_before plain).1
    obtain ⟨row, hr⟩ := rowAt_exists positive bound
    exact completeFrozenMarks_event_geometry hr h.valid (events row hr)
  · have missing : rowAt before owner = none := by
      cases atRow : rowAt before owner with
      | none => rfl
      | some row => have := (rowAt_bounds atRow).2; omega
    simpa only [completeFrozenMarks, missing] using
      And.intro h.valid (fun i => Eq.refl (predecessor before i))

/-- Endpoint transport also follows from the same prior verified events. -/
theorem scanPriorVerifiedEvents_endpoint_transport {lambda : Ordinal.{u}} {initial : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {r : Nat}
    (verified : ScanPriorVerifiedEvents initial initialTheta initialEmbedding r) :
    ScanPriorEndpointTransport initial initialTheta initialEmbedding r := by
  have geometry := scanPriorVerifiedEvents_geometry verified
  apply scanPriorEndpointTransport_of_events _ verified
  intro before history owner reach earlier
  obtain ⟨theta, embedding, labelled⟩ := scanReach_rank_lift reach initialTheta initialEmbedding
  exact (geometry before history owner theta embedding labelled earlier).1

end FullMarkedBLP

