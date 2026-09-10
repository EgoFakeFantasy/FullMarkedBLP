import FullMarkedBLP.RecordedWordWidthBound
import FullMarkedBLP.ScanGeneralOwnerEdges
import FullMarkedBLP.NativeWalkUnique
import FullMarkedBLP.CompletionRowClosure

namespace FullMarkedBLP

/-- A verified completion cannot read a wider packet than its head record.
This is used for earlier events; it does not establish the current event's
parallel-column identification from its own conclusion. -/
theorem scanRankReach_verified_completion_width {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {current : Row} (hr : rowAt a r = some current)
    {y : Nat} {sources headSources : List Nat} (hm : y ∈ current.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources)
    (headRecord : (y, headSources) ∈ rec)
    (verified : CompletionEventGeometry
      (processed.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding) :
    sources.length ≤ headSources.length := by
  have increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j := by
    intro i j lt bound
    apply verified.1.increasing i j lt
    simpa only [completeMarks_fold_length] using bound
  obtain ⟨front, terminal, last, delta, computed, record, cap, saved, covered⟩ :=
    scanRankReach_frozen_recorded_word_bounded_coverage reach entryRealization geometry increasing
      processed events verified.1.valid hr hm hc
  have member := recordAt_mem record
  have bounds := scanRankReach_record_source_bounds reach
    (fun before history owner oldTheta oldEmbedding prior bound =>
      (geometry before history owner oldTheta oldEmbedding prior bound).1) member
  have agreement : rankCutoffAgreement delta.val
      (rankWordEmbedding embedding (front ++ [terminal])) (embedding r) := by
    intro u z hu hz
    simpa only [rankWordEmbedding_apply] using (saved u z hu hz).symm
  have rb := rowAt_bounds hr
  obtain ⟨row, atRow⟩ := rowAt_exists
    (a := processed.foldl (fun current z => completeMark current rec r z) a) rb.1
    (by simpa only [completeMarks_fold_length] using rb.2)
  obtain ⟨_, _, _, _, _, _, _, nodup, _, _, _, packet⟩ := verified.2 row sources atRow hc
  by_cases le : sources.length ≤ headSources.length
  · exact le
  · obtain ⟨x, hx, rank⟩ := exists_source_at_rank nodup (j := headSources.length) (by omega)
    have small := covered headSources.length (by omega)
    have actual := rankAgreement_reads_visible_target agreement delta.property.le
      (covered _ (by rw [rank]; omega))
      (scanRankReach_record_word_edges reach member (fun z hz => (bounds z hz).le) front x hx)
    have same := (packet x hx).symm.trans actual
    rw [rank] at same
    rw [← same] at small
    have upper := cap headSources headRecord
    have bad : theta (y + headSources.length + 1) < theta (y + headSources.length + 1) := by
      have small' : theta (y + headSources.length + 1) < delta := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using small
      exact lt_of_lt_of_le small' upper
    exact False.elim (lt_irrefl _ bad)

end FullMarkedBLP
