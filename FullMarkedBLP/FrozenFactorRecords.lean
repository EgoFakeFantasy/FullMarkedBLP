import FullMarkedBLP.CompletionFactorRecords
import FullMarkedBLP.FrozenRecordDecision

namespace FullMarkedBLP

/-- All factors retain records at actual intermediate frozen successful events. -/
theorem scanRankReach_frozen_all_factor_records {lambda : Ordinal.{u}} {initial a : Pattern}
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
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∀ word, computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some word →
      ∀ factor ∈ word.dropLast, ∃ ss, (factor, ss) ∈ rec := by
  have recordEq := realized_frozen_completionRecord_eq currentReal processed events hr hm
  have entranceSuccess : completionRecord a rec r y = some sources := recordEq.symm.trans hc
  have records := scanRankReach_completion_all_factor_records reach entryReal currentReal geometry transport hr hm entranceSuccess
  obtain ⟨k, source, xs, delta, hk, hy, hs, trace, _, _⟩ := currentReal.marked r row y hr hm
  have old : MarkTrace a r y xs := ⟨row, k, source, hr, hm, hk, hy, hs, trace⟩
  have oldComputed := computeMarkTrace_complete currentReal.valid old
  have moved := frozen_fold_preserves_historical_trace processed events old
  have newComputed := computeMarkTrace_complete (frozen_fold_coreValid processed currentReal.valid events) moved
  intro word computed
  have eq : word = xs := Option.some.inj (computed.symm.trans newComputed)
  simpa only [eq] using records xs oldComputed

end FullMarkedBLP
