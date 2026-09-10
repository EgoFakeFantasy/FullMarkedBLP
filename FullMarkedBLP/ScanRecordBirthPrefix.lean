import FullMarkedBLP.ScanPrefix

namespace FullMarkedBLP

/-- A retained record comes with its actual birth event and the entire frozen
row prefix through the end of its inserted block. -/
theorem scanReach_record_origin_prefix {initial a : Pattern} {rec : Records} {r : Nat}
    (reach : ScanReach initial a rec r) {terminal : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) :
    ∃ before after history, ScanReach initial before history terminal ∧
      terminal ≤ before.length ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) ∧
      ∀ i, i ≤ terminal + sources.length → rowAt a i = rowAt after i := by
  induction reach with
  | start => simp at hm
  | @next before after history owner ss previous hb hn ih =>
    have keep : (terminal, sources) ∈ history →
        ∃ birth output oldHistory, ScanReach initial birth oldHistory terminal ∧
          terminal ≤ birth.length ∧
          native (completeFrozenMarks birth oldHistory terminal) terminal = some (output, sources) ∧
          ∀ i, i ≤ terminal + sources.length → rowAt after i = rowAt output i := by
      intro member
      obtain ⟨birth, output, oldHistory, oldReach, oldBound, nativeBirth, unchanged⟩ := ih member
      have bound := scanReach_record_targets_before previous member
      refine ⟨birth, output, oldHistory, oldReach, oldBound, nativeBirth, ?_⟩
      intro i hi
      exact (scan_step_prefix_rowAt hn (by omega)).trans (unchanged i hi)
    by_cases empty : ss = []
    · simp only [empty, List.isEmpty_nil, if_true] at hm
      exact keep hm
    · simp only [List.isEmpty_iff, empty, if_false] at hm
      rcases List.mem_cons.mp hm with eq | member
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
        exact ⟨before, after, history, previous, hb, hn, fun _ _ => rfl⟩
      · exact keep member

/-- Current-owner completions also preserve that entire historical block. -/
theorem scanReach_record_birth_frozen_prefix {initial a : Pattern} {rec : Records} {r : Nat}
    (reach : ScanReach initial a rec r) (processed : List Nat)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) :
    ∃ before after history, ScanReach initial before history terminal ∧
      terminal ≤ before.length ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) ∧
      ∀ i, i ≤ terminal + sources.length →
        rowAt (processed.foldl (fun current y => completeMark current rec r y) a) i = rowAt after i := by
  obtain ⟨before, after, history, oldReach, bound, birth, unchanged⟩ := scanReach_record_origin_prefix reach hm
  have earlier := scanReach_record_targets_before reach hm
  refine ⟨before, after, history, oldReach, bound, birth, ?_⟩
  intro i hi
  exact (completeMarks_fold_other_row processed (by omega : i ≠ r)).trans (unchanged i hi)

end FullMarkedBLP
