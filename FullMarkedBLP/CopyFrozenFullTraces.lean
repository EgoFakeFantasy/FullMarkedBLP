import FullMarkedBLP.CopyCompletionFullTraces
import FullMarkedBLP.FrozenRecordDecision

namespace FullMarkedBLP

/-- Full packet traces and widths persist to the actual intermediate frozen
state. The current mark event itself is not assumed verified. -/
theorem shortCopy_frozen_completion_full_traces {lambda : Ordinal.{u}} {parent copied a : Pattern}
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
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∃ word, computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some word ∧
      (∀ factor ∈ word.dropLast, ∃ ss, (factor, ss) ∈ rec ∧ ss.length = sources.length) ∧
      ∀ k, 0 < k → k ≤ sources.length →
        ∃ x ∈ sources, (sources.filter (· < x)).length = k - 1 ∧
          Trace (processed.foldl (fun current z => completeMark current rec r z) a)
            x (y + k) ((word.dropLast.map (fun i => i + k)) ++ [x]) := by
  have same := realized_frozen_completionRecord_eq currentReal processed events hr hm
  have entrance : completionRecord a rec r y = some sources := same.symm.trans hc
  obtain ⟨word, computed, widths, packet⟩ := shortCopy_completion_full_traces parentValid sat copy reach
    entryReal currentReal verified hr hm entrance
  have oldMark := computeMarkTrace_sound hr hm computed
  have transported := frozen_fold_preserves_historical_trace processed events oldMark
  have valid := frozen_fold_coreValid processed currentReal.valid events
  have predecessors := frozen_fold_preserves_predecessors processed events
  refine ⟨word, computeMarkTrace_complete valid transported, widths, ?_⟩
  intro k hk hkt
  obtain ⟨x, member, rank, trace⟩ := packet k hk hkt
  exact ⟨x, member, rank, (trace_iff_of_predecessor_eq predecessors).mpr trace⟩

end FullMarkedBLP
