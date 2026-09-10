import FullMarkedBLP.ScanFrozenDirectRealization

namespace FullMarkedBLP

/-- One sorted frozen-list step provides event evidence and the next realization. -/
theorem scanRankReach_frozen_direct_step {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (processed remaining : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (h : RankRowRealization (processed.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    {row currentRow : Row} (hr : rowAt a r = some row)
    (sorted : row.marks.Pairwise (· < ·)) (splitMarks : row.marks = processed ++ y :: remaining)
    (currentAt : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some currentRow)
    (ht : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some [y, s]) :
    CompletionEventGeometry (processed.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding ∧
    RankRowRealization
      (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y) theta embedding := by
  have hm : y ∈ row.marks := by rw [splitMarks]; simp
  have earlier : ∀ z ∈ processed, z < y := by
    have ordered := sorted
    rw [splitMarks] at ordered
    intro z hz
    exact (List.pairwise_append.mp ordered).2.2 z hz y (by simp)
  exact ⟨scanRankReach_frozen_direct_event_geometry reach entryRealization geometry
      processed earlier events h hr hm currentAt ht,
    scanRankReach_frozen_direct_realization reach entryRealization geometry
      processed earlier events h hr hm currentAt ht⟩

end FullMarkedBLP

