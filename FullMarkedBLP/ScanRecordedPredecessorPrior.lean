import FullMarkedBLP.ScanPrefix

namespace FullMarkedBLP

/-- Recorded source edges require validity only at strictly earlier entrances.
This form can be used inside the event induction without future validity. -/
theorem scanReach_record_predecessor_prior {initial a : Pattern} {rec : Records} {cursor : Nat}
    (reach : ScanReach initial a rec cursor)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    {terminal x : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec)
    (hx : x ∈ sources) :
    predecessor a (terminal + ((sources.filter (· < x)).length + 1)) = some x := by
  revert entrances
  induction reach with
  | start => simp at hm
  | @next before after history owner ss previous hb hn ih =>
    intro entrances
    have keep : (terminal, sources) ∈ history →
        predecessor after (terminal + ((sources.filter (· < x)).length + 1)) = some x := by
      intro hold
      have bound := scanReach_record_targets_before previous hold
      have rank : (sources.filter (· < x)).length < sources.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
      have edge := ih hold (fun a rec r reach hlt => entrances a rec r reach (by omega))
      simpa only [predecessor, scan_step_prefix_rowAt hn
        (by omega : terminal + ((sources.filter (· < x)).length + 1) < owner)] using edge
    by_cases hs : ss = []
    · simp only [hs, List.isEmpty_nil, if_true] at hm
      exact keep hm
    · simp only [List.isEmpty_iff, hs, if_false] at hm
      rcases List.mem_cons.mp hm with he | hold
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact native_source_predecessor (entrances before history terminal previous (by omega)) hn hx
      · exact keep hold

theorem scanReach_record_sources_below_prior {initial a : Pattern} {rec : Records} {cursor : Nat}
    (reach : ScanReach initial a rec cursor)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) :
    ∀ x ∈ sources, x < terminal := by
  have bound := scanReach_record_targets_before reach hm
  obtain ⟨before, after, history, previous, _, hn⟩ := scanReach_record_origin reach hm
  have hs := native_sources_of_success hn
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  exact nativeSources_below_owner (entrances before history terminal previous (by omega)) hr hs

/-- The literal recorded trace needs neither current nor future validity. -/
theorem scanReach_record_trace_prior {initial a : Pattern} {rec : Records} {cursor : Nat}
    (reach : ScanReach initial a rec cursor)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    {terminal x : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec)
    (hx : x ∈ sources) :
    Trace a x (terminal + ((sources.filter (· < x)).length + 1))
      [terminal + ((sources.filter (· < x)).length + 1), x] := by
  have bound := scanReach_record_sources_below_prior reach entrances hm x hx
  exact Trace.next (by omega) (scanReach_record_predecessor_prior reach entrances hm hx) Trace.stop

/-- Recorded direct traces survive every prefix of the current frozen-mark
fold, without assuming that any current completion has already been verified. -/
theorem scanReach_record_trace_frozen_prefix {initial a : Pattern} {rec : Records} {cursor : Nat}
    (reach : ScanReach initial a rec cursor)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (processed : List Nat) {terminal x : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) (hx : x ∈ sources) :
    Trace (processed.foldl (fun current y => completeMark current rec cursor y) a)
      x (terminal + ((sources.filter (· < x)).length + 1))
      [terminal + ((sources.filter (· < x)).length + 1), x] := by
  have source := scanReach_record_sources_below_prior reach entrances hm x hx
  have bound := scanReach_record_targets_before reach hm
  have rank : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have edge := scanReach_record_predecessor_prior reach entrances hm hx
  apply Trace.next (by omega) _ Trace.stop
  simpa only [predecessor, completeMarks_fold_other_row processed
    (by omega : terminal + ((sources.filter (· < x)).length + 1) ≠ cursor)] using edge

end FullMarkedBLP


