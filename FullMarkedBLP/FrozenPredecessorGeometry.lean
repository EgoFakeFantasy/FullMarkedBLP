import FullMarkedBLP.FrozenHistoricalTrace

namespace FullMarkedBLP

/-- The same event packet that preserves old marked words also preserves all
predecessors in the actual completeMark result. -/
theorem completionEvent_preserves_predecessors {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat} (event : CompletionEventGeometry a rec r y theta embedding) :
    ∀ i, predecessor (completeMark a rec r y) i = predecessor a i := by
  cases hr : rowAt a r with
  | none => intro i; simp [completeMark, hr]
  | some row =>
    cases hc : completionRecord a rec r y with
    | none => intro i; simp [completeMark, hr, hc]
    | some sources =>
      obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
        event.2 row sources hr hc
      have preserved := (rankRealization_completion_core_and_p event.1 hr hp hk hy hnext
        hs bounds gap beforeOwner packet).2
      simpa only [completeMark, hr, hc] using predecessor_set_eq hr (preserved.trans hp.symm)

/-- Predecessor preservation composes over actual frozen-prefix states. -/
theorem frozen_fold_preserves_predecessors {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r : Nat} (frozen : List Nat)
    (events : ∀ processed y suffix, frozen = processed ++ y :: suffix →
      CompletionEventGeometry
        (processed.foldl (fun current mark => completeMark current rec r mark) a) rec r y theta embedding) :
    ∀ i, predecessor (frozen.foldl (fun current mark => completeMark current rec r mark) a) i =
      predecessor a i := by
  induction frozen generalizing a with
  | nil => intro i; rfl
  | cons y rest ih =>
    have first := completionEvent_preserves_predecessors (events [] y rest rfl)
    have later := ih (a := completeMark a rec r y) (by
      intro processed next suffix he
      have event := events (y :: processed) next suffix (by simp only [List.cons_append, he])
      simpa only [List.foldl_cons] using event)
    intro i
    exact (later i).trans (first i)

theorem completionEvent_coreValid {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat} (event : CompletionEventGeometry a rec r y theta embedding) :
    ∀ i out, rowAt (completeMark a rec r y) i = some out → out.CoreValid i := by
  cases hr : rowAt a r with
  | none => simpa only [completeMark, hr] using event.1.valid
  | some row =>
    cases hc : completionRecord a rec r y with
    | none => simpa only [completeMark, hr, hc] using event.1.valid
    | some sources =>
      obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
        event.2 row sources hr hc
      have newValid := (rankRealization_completion_core_and_p event.1 hr hp hk hy hnext
        hs bounds gap beforeOwner packet).1
      intro i out hout
      simp only [completeMark, hr, hc] at hout
      by_cases hi : i = r
      · subst i
        rw [rowAt_set_self hr] at hout
        cases Option.some.inj hout
        exact newValid
      · rw [rowAt_set_other hr hi] at hout
        exact event.1.valid i out hout

theorem frozen_fold_coreValid {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r : Nat} (frozen : List Nat)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (events : ∀ processed y suffix, frozen = processed ++ y :: suffix →
      CompletionEventGeometry
        (processed.foldl (fun current mark => completeMark current rec r mark) a) rec r y theta embedding) :
    ∀ i row, rowAt (frozen.foldl (fun current mark => completeMark current rec r mark) a) i = some row →
      row.CoreValid i := by
  induction frozen generalizing a with
  | nil => exact valid
  | cons y rest ih =>
    apply ih (completionEvent_coreValid (events [] y rest rfl))
    intro processed next suffix he
    have event := events (y :: processed) next suffix (by simp only [List.cons_append, he])
    simpa only [List.foldl_cons] using event

/-- Actual frozen completion supplies both local scan-geometry conclusions. -/
theorem completeFrozenMarks_event_geometry {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r : Nat} {row : Row} (hr : rowAt a r = some row)
    (valid : ∀ i rw, rowAt a i = some rw → rw.CoreValid i)
    (events : ∀ processed y suffix, row.marks = processed ++ y :: suffix →
      CompletionEventGeometry
        (processed.foldl (fun current mark => completeMark current rec r mark) a) rec r y theta embedding) :
    (∀ i rw, rowAt (completeFrozenMarks a rec r) i = some rw → rw.CoreValid i) ∧
      (∀ i, predecessor (completeFrozenMarks a rec r) i = predecessor a i) := by
  simp only [completeFrozenMarks, hr]
  exact ⟨frozen_fold_coreValid row.marks valid events, frozen_fold_preserves_predecessors row.marks events⟩

end FullMarkedBLP



