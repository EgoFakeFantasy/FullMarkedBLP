import FullMarkedBLP.ScanRecordOrigin

namespace FullMarkedBLP

theorem completeMark_other_row {a : Pattern} {rec : Records} {r y i : Nat}
    (hi : i ≠ r) : rowAt (completeMark a rec r y) i = rowAt a i := by
  unfold completeMark
  split
  next row sources hrow hrec => exact rowAt_set_other hrow hi
  next => rfl

theorem completeMarks_fold_other_row (ys : List Nat) {a : Pattern} {rec : Records} {r i : Nat}
    (hi : i ≠ r) :
    rowAt (ys.foldl (fun current y => completeMark current rec r y) a) i = rowAt a i := by
  induction ys generalizing a with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [ih, completeMark_other_row hi]

theorem completeFrozenMarks_other_row {a : Pattern} {rec : Records} {r i : Nat}
    (hi : i ≠ r) : rowAt (completeFrozenMarks a rec r) i = rowAt a i := by
  unfold completeFrozenMarks
  split
  next => rfl
  next => exact completeMarks_fold_other_row _ hi

theorem scan_step_prefix_rowAt {a b : Pattern} {rec : Records} {r : Nat} {sources : List Nat}
    (hn : native (completeFrozenMarks a rec r) r = some (b, sources))
    {i : Nat} (hi : i < r) : rowAt b i = rowAt a i := by
  rw [native_prefix_rowAt hn hi, completeFrozenMarks_other_row (by omega : i ≠ r)]

/-- All stored native source rows lie in the already-scanned prefix. -/
theorem scanReach_record_targets_before {initial a : Pattern} {rec : Records} {r : Nat}
    (h : ScanReach initial a rec r) {terminal : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) : terminal + sources.length < r := by
  induction h with
  | start => simp at hm
  | @next before after history owner ss previous hb hn ih =>
    by_cases hs : ss = []
    · simp only [hs, List.isEmpty_nil, ↓reduceIte] at hm
      have hh := ih hm
      omega
    · simp only [List.isEmpty_iff, hs, ↓reduceIte] at hm
      rcases List.mem_cons.mp hm with he | he
      · obtain ⟨he1, he2⟩ := Prod.mk.inj he
        subst terminal
        subst sources
        omega
      · have hh := ih he
        omega

/-- Native source-predecessor equations survive every later scan step. -/
theorem scanReach_record_predecessor {initial a : Pattern} {rec : Records} {r : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {terminal x : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) (hx : x ∈ sources) :
    predecessor a (terminal + ((sources.filter (· < x)).length + 1)) = some x := by
  induction reach with
  | start => simp at hm
  | @next before after history owner ss previous hb hn ih =>
    have preserve : (terminal, sources) ∈ history →
        predecessor after (terminal + ((sources.filter (· < x)).length + 1)) = some x := by
      intro he
      have ht := scanReach_record_targets_before previous he
      have hlt : (sources.filter (· < x)).length < sources.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
      have hp := ih he
      simpa only [predecessor, scan_step_prefix_rowAt hn
        (by omega : terminal + ((sources.filter (· < x)).length + 1) < owner)] using hp
    by_cases hs : ss = []
    · simp only [hs, List.isEmpty_nil, ↓reduceIte] at hm
      exact preserve hm
    · simp only [List.isEmpty_iff, hs, ↓reduceIte] at hm
      rcases List.mem_cons.mp hm with he | he
      · obtain ⟨he1, he2⟩ := Prod.mk.inj he
        subst terminal
        subst sources
        exact native_source_predecessor (historyValid before history owner previous) hn hx
      · exact preserve he

theorem scanReach_record_trace {initial a : Pattern} {rec : Records} {r : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {terminal x : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) (hx : x ∈ sources) :
    Trace a x (terminal + ((sources.filter (· < x)).length + 1))
      [terminal + ((sources.filter (· < x)).length + 1), x] := by
  have hb := scanReach_record_sources_below historyValid reach hm x hx
  exact Trace.next (by omega) (scanReach_record_predecessor historyValid reach hm hx) Trace.stop

end FullMarkedBLP



