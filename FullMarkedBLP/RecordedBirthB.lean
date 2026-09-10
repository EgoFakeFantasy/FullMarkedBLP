import FullMarkedBLP.ScanStepEndpointBound
import FullMarkedBLP.RecordedBirthBExact

namespace FullMarkedBLP

/-- Retained records inherit their actual birth-step endpoint estimate.
Only strictly earlier scan entrances and their verified events are required. -/
theorem scanReach_record_birth_b_bound {lambda : Ordinal.{u}}
    {initial a : Pattern} {rec : Records} {r terminal w : Nat} {sources : List Nat}
    (reach : ScanReach initial a rec r)
    (prior : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∃ (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda),
        RankRowRealization before theta embedding ∧
        ∀ row, rowAt before owner = some row →
          ∀ done mark suffix, row.marks = done ++ mark :: suffix →
            CompletionEventGeometry
              (done.foldl (fun current y => completeMark current history owner y) before)
              history owner mark theta embedding)
    (member : (terminal, sources) ∈ rec) {bottom : Row}
    (atBottom : rowAt a terminal = some bottom) (bottomB : bottom.b = some w) :
    ∃ before after history row v,
      ScanReach initial before history terminal ∧
      rowAt before terminal = some row ∧ row.b = some v ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) ∧
      (∀ i, i ≤ terminal + sources.length → rowAt a i = rowAt after i) ∧
      w ≤ v + if v ∈ row.marks then
        ((completionRecord before history terminal v).getD []).length else 0 := by
  obtain ⟨before, after, history, row, v, origin, atRow, value, birth, unchanged, exactValue⟩ :=
    scanReach_record_birth_b_exact reach prior member atBottom bottomB
  exact ⟨before, after, history, row, v, origin, atRow, value, birth, unchanged, exactValue.le⟩

end FullMarkedBLP
