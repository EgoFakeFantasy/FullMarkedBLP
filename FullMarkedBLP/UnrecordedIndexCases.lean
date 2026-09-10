import FullMarkedBLP.ScanIndexOrigin
import FullMarkedBLP.ScanRecordedTargetB

namespace FullMarkedBLP

/-- A passed index without its own record is an interior target or an empty birth. -/
theorem scanReach_unrecorded_index_cases {initial a : Pattern} {rec : Records} {r i : Nat}
    (reach : ScanReach initial a rec r)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ j row, rowAt (completeFrozenMarks before history owner) j = some row → row.CoreValid j)
    (positive : 0 < i) (passed : i < r)
    (missing : ∀ ss, (i, ss) ∉ rec) :
    ((rowAt a i).bind Row.b = some (i - 1)) ∨
    (∃ before history, ScanReach initial before history i ∧
      nativeSources (completeFrozenMarks before history i) i = some [] ∧
      rowAt a i = rowAt (completeFrozenMarks before history i) i) := by
  rcases scanReach_processed_index_origin reach positive passed with block | empty
  · obtain ⟨owner, sources, member, lo, hi⟩ := block
    have strict : owner < i := by
      have ne : owner ≠ i := by
        intro eq
        subst owner
        exact missing sources member
      omega
    have edge := scanReach_record_target_b reach entrances member
      (k := i - owner) (by omega) (by omega)
    left
    simpa only [Nat.add_sub_of_le lo] using edge
  · obtain ⟨before, after, history, prior, birth, unchanged⟩ := empty
    have source := native_sources_of_success birth
    obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp birth
    have identity := native_empty hr source
    have eq : after = completeFrozenMarks before history i :=
      (Prod.mk.inj (Option.some.inj (birth.symm.trans identity))).1
    exact Or.inr ⟨before, history, prior, source, by simpa only [eq] using unchanged⟩

end FullMarkedBLP

