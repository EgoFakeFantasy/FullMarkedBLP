import FullMarkedBLP.CopyCompletionHeadPacket

namespace FullMarkedBLP

/-- A previously verified frozen completion reads exactly its head-record width.
The lower bound is independent of the event's packet; the upper bound uses
that already verified packet. Later events may use this equality. -/
theorem shortCopy_verified_completion_width_eq {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    {sources : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources)
    (event : CompletionEventGeometry
      (processed.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding) :
    ∃ headSources, (y, headSources) ∈ rec ∧ sources.length = headSources.length := by
  have same := realized_frozen_completionRecord_eq currentReal processed events hr hm
  have entrance : completionRecord a rec r y = some sources := same.symm.trans hc
  obtain ⟨_, headSources, _, record, lower, _⟩ :=
    shortCopy_completion_head_packet parentValid sat copy reach entryReal currentReal verified hr hm entrance
  have upper := scanRankReach_verified_completion_width reach entryReal
    (scanPriorVerifiedEvents_geometry verified) processed events hr hm hc record event
  exact ⟨headSources, record, by omega⟩

end FullMarkedBLP
