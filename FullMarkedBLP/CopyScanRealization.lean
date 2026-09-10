import FullMarkedBLP.CopyFrozenFold
import FullMarkedBLP.NativeRankRealization

namespace FullMarkedBLP

/-- Strong induction on the actual scan cursor simultaneously verifies every
entrance and every frozen event after a Sat short copy. No prior-event or
intermediate-realization hypothesis remains. -/
theorem shortCopy_scan_realization {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {parent copied a : Pattern} {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding) :
    RankRowRealization a theta embedding ∧
    ∀ row, rowAt a r = some row →
      RankRowRealization (completeFrozenMarks a rec r) theta embedding ∧
      ∀ done y suffix, row.marks = done ++ y :: suffix →
        CompletionEventGeometry (done.foldl (fun current z => completeMark current rec r z) a)
          rec r y theta embedding := by
  induction r using Nat.strong_induction_on generalizing a rec theta embedding with
  | h r ih =>
    have verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r := by
      intro before history owner oldTheta oldEmbedding prior earlier
      have result := ih owner earlier prior
      exact ⟨result.1, fun row hr => (result.2 row hr).2⟩
    have currentReal : RankRowRealization a theta embedding := by
      cases reach with
      | start => exact entryReal
      | @next before after history owner sources oldTheta oldEmbedding prior bound birth =>
        have result := ih owner (by omega) prior
        have positive := (scanReach_records_before
          (scanEmbeddingReach_forget (scanRankReach_embeddings prior))).1
        obtain ⟨row, hr⟩ := rowAt_exists positive bound
        exact rankRowRealization_native hl (result.2 row hr).1 birth
    exact ⟨currentReal, fun row hr => shortCopy_frozen_fold parentValid sat copy reach entryReal currentReal verified hr⟩

end FullMarkedBLP
