import FullMarkedBLP.FrozenPredecessorGeometry
import FullMarkedBLP.ScanPriorGeometry

namespace FullMarkedBLP

/-- Prior event hypotheses imply the scan geometry used for exact historical
word transport; no current or future event is included. -/
theorem scanPriorGeometry_of_events {lambda : Ordinal.{u}} {initial : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {cursor : Nat}
    (prior : ∀ before history owner oldTheta oldEmbedding,
      ScanRankReach initial initialTheta initialEmbedding before history owner oldTheta oldEmbedding →
      owner < cursor →
      (∀ i row, rowAt before i = some row → row.CoreValid i) ∧
      (∀ row, rowAt before owner = some row →
        ∀ processed y suffix, row.marks = processed ++ y :: suffix →
          CompletionEventGeometry
            (processed.foldl (fun current mark => completeMark current history owner mark) before)
            history owner y oldTheta oldEmbedding)) :
    ScanPriorGeometry initial initialTheta initialEmbedding cursor := by
  intro before history owner oldTheta oldEmbedding reach bound
  obtain ⟨valid, events⟩ := prior before history owner oldTheta oldEmbedding reach bound
  cases hr : rowAt before owner with
  | none =>
    simp only [completeFrozenMarks, hr]
    exact ⟨valid, fun _ => True.intro⟩
  | some row => exact completeFrozenMarks_event_geometry hr valid (events row hr)

end FullMarkedBLP

