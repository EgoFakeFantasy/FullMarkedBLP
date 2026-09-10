import FullMarkedBLP.VerifiedCompletionWidth
import FullMarkedBLP.CompletionHeadRecord
import FullMarkedBLP.FrozenRecordDecision

namespace FullMarkedBLP

/-- A successful verified frozen event supplies its own head record and the
packet-width bound. Only prior endpoint transport is required for existence. -/
theorem scanRankReach_frozen_verified_head_width {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    {sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization initial initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (transport : ScanPriorEndpointTransport initial initialTheta initialEmbedding r)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources)
    (verified : CompletionEventGeometry
      (processed.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding) :
    ∃ ss, (y, ss) ∈ rec ∧ sources.length ≤ ss.length := by
  have same := realized_frozen_completionRecord_eq currentReal processed events hr hm
  have entrance : completionRecord a rec r y = some sources := same.symm.trans hc
  obtain ⟨ss, record⟩ := scanRankReach_completion_head_record reach entryReal currentReal geometry transport hr hm entrance
  exact ⟨ss, record, scanRankReach_verified_completion_width reach entryReal geometry processed events
    hr hm hc record verified⟩

end FullMarkedBLP

