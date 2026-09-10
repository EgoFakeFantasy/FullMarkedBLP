import FullMarkedBLP.FrozenGuardInvariant
import FullMarkedBLP.FrozenPredecessorGeometry

namespace FullMarkedBLP

/-- Every original realized mark keeps its entire completion decision through
an already verified frozen prefix, for words of arbitrary length. -/
theorem realized_frozen_completionRecord_eq {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat} (h : RankRowRealization a theta embedding)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks) :
    completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y =
      completionRecord a rec r y := by
  have valid := frozen_fold_coreValid processed h.valid events
  obtain ⟨k, source, xs, delta, hk, hy, hs, trace, _, _⟩ := h.marked r row y hr hm
  have mark : MarkTrace a r y xs := ⟨row, k, source, hr, hm, hk, hy, hs, trace⟩
  have moved := frozen_fold_preserves_historical_trace processed events mark
  apply frozen_completionRecord_eq processed (computeMarkTrace_complete h.valid mark)
    (computeMarkTrace_complete valid moved)
  intro i hi
  have bound := trace_member_le_head h.valid trace ((List.dropLast_sublist xs).subset hi)
  exact lt_of_le_of_lt bound ((h.proper r row hr).2 y hm).1

/-- Successful frozen completions after a short copy keep every word factor
inside the copied region; the original Sat prefix cannot supply a record. -/
theorem shortCopy_frozen_completion_factor_region {lambda : Ordinal.{u}}
    {parent copied a : Pattern} {rec : Records} {r y : Nat}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (parentValid : ∀ i rw, rowAt parent i = some rw → rw.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanReach copied a rec r) (h : RankRowRealization a theta embedding)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row : Row} {sources : List Nat} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∃ xs, MarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y xs ∧
      ∀ factor ∈ xs.dropLast, parent.length ≤ factor := by
  have original : completionRecord a rec r y = some sources :=
    (realized_frozen_completionRecord_eq h processed events hr hm).symm.trans hc
  obtain ⟨xs, trace, region⟩ := shortCopy_completion_factor_region parentValid h.valid sat copy reach hr hm original
  exact ⟨xs, frozen_fold_preserves_historical_trace processed events trace, region⟩

end FullMarkedBLP


