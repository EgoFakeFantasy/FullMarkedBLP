import FullMarkedBLP.ScanRecordBirthPrefix
import FullMarkedBLP.ScanRecordedTargetB

namespace FullMarkedBLP

/-- A lower retained record was already present at a higher record's actual
birth, and the higher birth block is still unchanged. -/
theorem scanReach_ordered_record_birth {initial a : Pattern} {rec : Records} {r upper lower : Nat}
    {upperSources lowerSources : List Nat} (reach : ScanReach initial a rec r)
    (upperMem : (upper, upperSources) ∈ rec) (lowerMem : (lower, lowerSources) ∈ rec)
    (lt : lower < upper) :
    ∃ before after history, ScanReach initial before history upper ∧
      (lower, lowerSources) ∈ history ∧
      native (completeFrozenMarks before history upper) upper = some (after, upperSources) ∧
      ∀ i, i ≤ upper + upperSources.length → rowAt a i = rowAt after i := by
  induction reach with
  | start => simp at upperMem
  | @next before after history owner ss previous hb hn ih =>
    have keep : (upper, upperSources) ∈ history → (lower, lowerSources) ∈ history →
        ∃ birth output oldHistory, ScanReach initial birth oldHistory upper ∧
          (lower, lowerSources) ∈ oldHistory ∧
          native (completeFrozenMarks birth oldHistory upper) upper = some (output, upperSources) ∧
          ∀ i, i ≤ upper + upperSources.length → rowAt after i = rowAt output i := by
      intro up lo
      obtain ⟨birth, output, oldHistory, oldReach, oldLower, nativeBirth, unchanged⟩ := ih up lo
      have bound := scanReach_record_targets_before previous up
      refine ⟨birth, output, oldHistory, oldReach, oldLower, nativeBirth, ?_⟩
      intro i hi
      exact (scan_step_prefix_rowAt hn (by omega)).trans (unchanged i hi)
    by_cases empty : ss = []
    · simp only [empty, List.isEmpty_nil, if_true] at upperMem lowerMem
      exact keep upperMem lowerMem
    · simp only [List.isEmpty_iff, empty, if_false] at upperMem lowerMem
      rcases List.mem_cons.mp upperMem with eq | up
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
        have lo : (lower, lowerSources) ∈ history := by
          rcases List.mem_cons.mp lowerMem with eq | lo
          · have same := (Prod.mk.inj eq).1
            omega
          · exact lo
        exact ⟨before, after, history, previous, lo, hn, fun _ _ => rfl⟩
      · have bound := scanReach_record_targets_before previous up
        have lo : (lower, lowerSources) ∈ history := by
          rcases List.mem_cons.mp lowerMem with eq | lo
          · have same := (Prod.mk.inj eq).1
            omega
          · exact lo
        exact keep up lo

/-- The lower record's entire target B chain is available at the higher
record's actual native entrance, from strictly earlier validity alone. -/
theorem scanReach_ordered_birth_target_chain {initial a : Pattern} {rec : Records} {r upper lower : Nat}
    {upperSources lowerSources : List Nat} (reach : ScanReach initial a rec r)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (upperMem : (upper, upperSources) ∈ rec) (lowerMem : (lower, lowerSources) ∈ rec)
    (lt : lower < upper) :
    ∃ before after history, ScanReach initial before history upper ∧
      (lower, lowerSources) ∈ history ∧
      native (completeFrozenMarks before history upper) upper = some (after, upperSources) ∧
      (∀ i, i ≤ upper + upperSources.length → rowAt a i = rowAt after i) ∧
      ∀ k, 0 < k → k ≤ lowerSources.length →
        (rowAt (completeFrozenMarks before history upper) (lower + k)).bind Row.b = some (lower + k - 1) := by
  obtain ⟨before, after, history, prior, member, birth, unchanged⟩ :=
    scanReach_ordered_record_birth reach upperMem lowerMem lt
  have upperBound := scanReach_record_targets_before reach upperMem
  have lowerBound := scanReach_record_targets_before prior member
  refine ⟨before, after, history, prior, member, birth, unchanged, ?_⟩
  intro k hk hkt
  rw [completeFrozenMarks_other_row (by omega : lower + k ≠ upper)]
  exact scanReach_record_target_b prior
    (fun before history owner old bound => entrances before history owner old (by omega)) member hk hkt

end FullMarkedBLP

