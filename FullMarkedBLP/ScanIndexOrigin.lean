import FullMarkedBLP.ScanRecordBirthPrefix

namespace FullMarkedBLP

/-- Every passed index is in a retained block or was visited by an empty native step. -/
theorem scanReach_processed_index_origin {initial a : Pattern} {rec : Records} {r i : Nat}
    (reach : ScanReach initial a rec r) (positive : 0 < i) (passed : i < r) :
    (∃ owner sources, (owner, sources) ∈ rec ∧ owner ≤ i ∧ i ≤ owner + sources.length) ∨
    (∃ before after history, ScanReach initial before history i ∧
      native (completeFrozenMarks before history i) i = some (after, []) ∧
      rowAt a i = rowAt after i) := by
  induction reach with
  | start => omega
  | @next before after history owner sources prior bound birth ih =>
    by_cases earlier : i < owner
    · rcases ih earlier with block | empty
      · obtain ⟨base, ss, member, lo, hi⟩ := block
        left
        refine ⟨base, ss, ?_, lo, hi⟩
        by_cases noSources : sources = []
        · simpa only [noSources, List.isEmpty_nil, if_true] using member
        · simp only [List.isEmpty_iff, noSources, if_false]
          exact List.mem_cons_of_mem _ member
      · obtain ⟨input, output, oldHistory, oldReach, emptyBirth, unchanged⟩ := empty
        exact Or.inr ⟨input, output, oldHistory, oldReach, emptyBirth,
          (scan_step_prefix_rowAt birth earlier).trans unchanged⟩
    · by_cases noSources : sources = []
      · have eq : i = owner := by simp only [noSources, List.length_nil] at passed; omega
        subst i
        right
        exact ⟨before, after, history, prior, by simpa only [noSources] using birth, rfl⟩
      · left
        refine ⟨owner, sources, ?_, by omega, by omega⟩
        simp only [List.isEmpty_iff, noSources, if_false, List.mem_cons, true_or]

end FullMarkedBLP
