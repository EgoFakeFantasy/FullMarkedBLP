import FullMarkedBLP.RecordedWordDecomposition
import FullMarkedBLP.ScanBirthPacketEdges

namespace FullMarkedBLP

/-- Actual successful arbitrary-word completions read the semantic record packet through their owner embedding. Column identification is still separate. -/
theorem scanRankReach_frozen_recorded_owner_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (valid : ∀ i rw,
      rowAt (processed.foldl (fun current z => completeMark current rec r z) a) i = some rw → rw.CoreValid i)
    {current : Row} (hr : rowAt a r = some current)
    {y : Nat} {sources : List Nat} (hm : y ∈ current.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∃ (front : List Nat) (terminal last : Nat),
      computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y =
        some (front ++ [terminal, last]) ∧
      recordAt rec terminal = some sources ∧
      ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
        evalWord (fun i => rankOrdinalAction (embedding i)) front
          (theta (terminal + 1 + (sources.filter (· < x)).length)) := by
  obtain ⟨front, terminal, last, delta, computed, record, saved, covered⟩ :=
    scanRankReach_frozen_recorded_word_coverage h entryRealization geometry increasing processed events valid hr hm hc
  have member := recordAt_mem record
  have bounds := scanRankReach_record_source_bounds h
    (fun before history owner oldTheta oldEmbedding prior bound =>
      (geometry before history owner oldTheta oldEmbedding prior bound).1) member
  have agreement : rankCutoffAgreement delta.val
      (rankWordEmbedding embedding (front ++ [terminal])) (embedding r) := by
    intro u z hu hz
    simpa only [rankWordEmbedding_apply] using (saved u z hu hz).symm
  refine ⟨front, terminal, last, computed, record, ?_⟩
  intro x hx
  have rank : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  exact rankAgreement_reads_visible_target agreement delta.property.le (covered _ rank)
    (scanRankReach_record_word_edges h member (fun x hx => (bounds x hx).le) front x hx)

end FullMarkedBLP
