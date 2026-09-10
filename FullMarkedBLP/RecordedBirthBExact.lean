import FullMarkedBLP.ScanStepBExact
import FullMarkedBLP.ScanRecordBirthPrefix

namespace FullMarkedBLP

/-- Retained records inherit their actual birth-step exact endpoint value.
Only strictly earlier scan entrances and their verified events are required. -/
theorem scanReach_record_birth_b_exact {lambda : Ordinal.{u}}
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
      w = v + if v ∈ row.marks then
        ((completionRecord before history terminal v).getD []).length else 0 := by
  obtain ⟨before, after, history, oldReach, bound, birth, unchanged⟩ :=
    scanReach_record_origin_prefix reach member
  have earlier := scanReach_record_targets_before reach member
  obtain ⟨theta, embedding, h, events⟩ := prior before history terminal oldReach (by omega)
  have positive := ((scanReach_records_before reach).2 (terminal, sources) member).1
  obtain ⟨row, hr⟩ := rowAt_exists positive bound
  obtain ⟨v, hv⟩ := fromRight_exists (xs := row.core) (k := 2) (by decide)
    (h.valid terminal row hr).2.1
  have atBirth : rowAt after terminal = some bottom :=
    (unchanged terminal (by omega)).symm.trans atBottom
  exact ⟨before, after, history, row, v, oldReach, hr, hv, birth, unchanged,
    Option.some.inj (bottomB.symm.trans (scan_step_bottom_b_update h hr hv (events row hr) birth atBirth))⟩

end FullMarkedBLP

