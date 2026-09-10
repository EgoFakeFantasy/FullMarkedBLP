import FullMarkedBLP.NativeOutputTargetB

namespace FullMarkedBLP

/-- Every retained record keeps its consecutive B chain. Only native entrances
strictly preceding the current cursor need core validity. -/
theorem scanReach_record_target_b {initial a : Pattern} {rec : Records} {cursor : Nat}
    (reach : ScanReach initial a rec cursor)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec)
    {k : Nat} (hk : 0 < k) (hkt : k ≤ sources.length) :
    (rowAt a (terminal + k)).bind Row.b = some (terminal + k - 1) := by
  revert entrances
  induction reach with
  | start => simp at hm
  | @next before after history owner ss previous hb hn ih =>
    intro entrances
    have keep : (terminal, sources) ∈ history →
        (rowAt after (terminal + k)).bind Row.b = some (terminal + k - 1) := by
      intro hold
      have hbound := scanReach_record_targets_before previous hold
      rw [scan_step_prefix_rowAt hn (by omega : terminal + k < owner)]
      exact ih hold (fun before history oldOwner reach hlt =>
        entrances before history oldOwner reach (by omega))
    by_cases hs : ss = []
    · simp only [hs, List.isEmpty_nil, if_true] at hm
      exact keep hm
    · simp only [List.isEmpty_iff, hs, if_false] at hm
      rcases List.mem_cons.mp hm with he | hold
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact native_output_target_b (entrances before history terminal previous (by omega)) hn hk hkt
      · exact keep hold

end FullMarkedBLP
