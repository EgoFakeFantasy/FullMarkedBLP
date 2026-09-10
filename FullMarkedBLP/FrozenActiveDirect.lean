import FullMarkedBLP.FrozenPrefixInduction
import FullMarkedBLP.FrozenRecordDecision

namespace FullMarkedBLP

/-- Inactive marks may have arbitrary words; only successful events require the direct-word hypothesis. -/
theorem scanRankReach_active_direct_frozen_fold {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (h : RankRowRealization a theta embedding) {row : Row} (hr : rowAt a r = some row)
    (direct : ∀ done y suffix, row.marks = done ++ y :: suffix →
      ∀ sources, completionRecord (done.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources →
      ∃ source, computeMarkTrace (done.foldl (fun current z => completeMark current rec r z) a) r y = some [y, source]) :
    RankRowRealization (completeFrozenMarks a rec r) theta embedding ∧
    ∀ done y suffix, row.marks = done ++ y :: suffix →
      CompletionEventGeometry (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding := by
  have result := frozen_prefix_bootstrap
    (P := fun done y => CompletionEventGeometry
      (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding)
    (Q := fun done => RankRowRealization
      (done.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    row.marks h (by
      intro done y suffix splitMarks state events
      have rb := rowAt_bounds hr
      obtain ⟨currentRow, currentAt⟩ := rowAt_exists
        (a := done.foldl (fun current z => completeMark current rec r z) a) rb.1
        (by simpa only [completeMarks_fold_length] using rb.2)
      cases hc : completionRecord (done.foldl (fun current z => completeMark current rec r z) a) rec r y with
      | none =>
        have event : CompletionEventGeometry
            (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding := by
          refine ⟨state, ?_⟩
          intro other sources _ success
          rw [hc] at success
          contradiction
        refine ⟨event, ?_⟩
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [completeMark, currentAt, hc]
        exact state
      | some sources =>
        obtain ⟨source, computed⟩ := direct done y suffix splitMarks sources hc
        obtain ⟨event, next⟩ := scanRankReach_frozen_direct_step reach entryRealization geometry
          done suffix events state hr (h.proper r row hr).1 splitMarks currentAt computed
        exact ⟨event, by simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using next⟩)
  exact ⟨by simpa only [completeFrozenMarks, hr] using result.1, result.2⟩

/-- All successful-word checks can be made at the entrance, before the frozen fold. -/
theorem scanRankReach_entry_active_direct_frozen_fold {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (h : RankRowRealization a theta embedding) {row : Row} (hr : rowAt a r = some row)
    (direct : ∀ y ∈ row.marks, ∀ sources, completionRecord a rec r y = some sources →
      ∃ source, computeMarkTrace a r y = some [y, source]) :
    RankRowRealization (completeFrozenMarks a rec r) theta embedding ∧
    ∀ done y suffix, row.marks = done ++ y :: suffix →
      CompletionEventGeometry (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding := by
  have result := frozen_prefix_bootstrap
    (P := fun done y => CompletionEventGeometry
      (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding)
    (Q := fun done => RankRowRealization
      (done.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    row.marks h (by
      intro done y suffix splitMarks state events
      have rb := rowAt_bounds hr
      obtain ⟨currentRow, currentAt⟩ := rowAt_exists
        (a := done.foldl (fun current z => completeMark current rec r z) a) rb.1
        (by simpa only [completeMarks_fold_length] using rb.2)
      cases hc : completionRecord (done.foldl (fun current z => completeMark current rec r z) a) rec r y with
      | none =>
        have event : CompletionEventGeometry
            (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding := by
          refine ⟨state, ?_⟩
          intro other sources _ success
          rw [hc] at success
          contradiction
        refine ⟨event, ?_⟩
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [completeMark, currentAt, hc]
        exact state
      | some sources =>
        have mark : y ∈ row.marks := by rw [splitMarks]; simp
        have oldRecord : completionRecord a rec r y = some sources :=
          (realized_frozen_completionRecord_eq h done events hr mark).symm.trans hc
        obtain ⟨source, oldComputed⟩ := direct y mark sources oldRecord
        have oldTrace := computeMarkTrace_sound hr mark oldComputed
        have moved := frozen_fold_preserves_historical_trace done events oldTrace
        have computed := computeMarkTrace_complete state.valid moved
        obtain ⟨event, next⟩ := scanRankReach_frozen_direct_step reach entryRealization geometry
          done suffix events state hr (h.proper r row hr).1 splitMarks currentAt computed
        exact ⟨event, by simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using next⟩)
  exact ⟨by simpa only [completeFrozenMarks, hr] using result.1, result.2⟩

end FullMarkedBLP




