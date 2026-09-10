import FullMarkedBLP.CopyFrozenRealization

namespace FullMarkedBLP

/-- The complete frozen-mark fold after a Sat short copy preserves row
realization and verifies every event. Intermediate realizations, packet
geometry and restrictions on successful word length are not premises. -/
theorem shortCopy_frozen_fold {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    {row : Row} (hr : rowAt a r = some row) :
    RankRowRealization (completeFrozenMarks a rec r) theta embedding ∧
    ∀ done y suffix, row.marks = done ++ y :: suffix →
      CompletionEventGeometry (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding := by
  have result := frozen_prefix_bootstrap
    (P := fun done y => CompletionEventGeometry
      (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding)
    (Q := fun done => RankRowRealization
      (done.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    row.marks currentReal (by
      intro done y suffix splitMarks state events
      have rb := rowAt_bounds hr
      obtain ⟨currentRow, currentAt⟩ := rowAt_exists
        (a := done.foldl (fun current z => completeMark current rec r z) a) rb.1
        (by simpa only [completeMarks_fold_length] using rb.2)
      have hm : y ∈ row.marks := by rw [splitMarks]; simp
      have earlier : ∀ z ∈ done, z < y := by
        have sorted := (currentReal.proper r row hr).1
        rw [splitMarks] at sorted
        intro z hz
        exact (List.pairwise_append.mp sorted).2.2 z hz y (by simp)
      have event := shortCopy_frozen_event_geometry parentValid sat copy reach entryReal currentReal verified
        done earlier events state hr hm currentAt
      have next := shortCopy_frozen_realization parentValid sat copy reach entryReal currentReal verified
        done earlier events state hr hm currentAt
      exact ⟨event, by simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using next⟩)
  exact ⟨by simpa only [completeFrozenMarks, hr] using result.1, result.2⟩

end FullMarkedBLP
