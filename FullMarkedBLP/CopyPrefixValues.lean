import FullMarkedBLP.CopyRecordRegion
import FullMarkedBLP.ScanRankReach

namespace FullMarkedBLP

/-- The inherited prefix, including the first copied column, keeps its original
semantic assignments throughout a short-copy scan. -/
theorem shortCopy_scan_prefix_values {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding) :
    ∀ i, i ≤ parent.length → theta i = initialTheta i ∧ embedding i = initialEmbedding i := by
  induction reach with
  | start => intro i _; exact ⟨rfl, rfl⟩
  | @next before after history owner sources oldTheta oldEmbedding previous bound birth ih =>
    have fixed : ∀ i, i ≤ parent.length → shiftAfter owner sources.length i = i := by
      intro i hi
      by_cases empty : sources = []
      · simp [empty, shiftAfter]
      · have later := ScanRankReach.next previous bound birth
        have member : (owner, sources) ∈ (if sources.isEmpty then history else (owner, sources) :: history) := by
          simp [empty]
        have region := (shortCopy_scan_record_region parentValid sat copy
          (scanEmbeddingReach_forget (scanRankReach_embeddings later))).2 (owner, sources) member
        simp [shiftAfter, show ¬owner < i by dsimp only at region; omega]
    intro i hi
    have column := nativeColumnValues_preserves oldTheta
      (nativeFreshValues oldTheta (oldEmbedding owner) owner sources) owner sources.length i
    have emb := nativeEmbeddingValues_old oldEmbedding owner sources.length i
    rw [fixed i hi] at column emb
    exact ⟨column.trans (ih i hi).1, emb.trans (ih i hi).2⟩

end FullMarkedBLP
