import FullMarkedBLP.FrozenPredecessorGeometry

namespace FullMarkedBLP

/-- A verified completion increases the core length by twice the step increase. -/
theorem completionEvent_length_step_balance {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat}
    (event : CompletionEventGeometry a rec r y theta embedding)
    {row out : Row} (hr : rowAt a r = some row) (hout : rowAt (completeMark a rec r y) r = some out) :
    out.core.length + 2 * row.step = row.core.length + 2 * out.step := by
  cases success : completionRecord a rec r y with
  | none =>
    have same : out = row := Option.some.inj (hout.symm.trans (by simpa only [completeMark, hr, success] using hr))
    simp only [same]
  | some sources =>
    have atOut : rowAt (completeMark a rec r y) r = some (completeMarkRow row y sources) := by
      rw [completeMark, hr, success]
      exact rowAt_set_self hr
    have same : out = completeMarkRow row y sources := Option.some.inj (hout.symm.trans atOut)
    obtain ⟨k, p, next, hp, hk, hy, hn, nodup, bounds, gap, before, packet⟩ := event.2 row sources hr success
    obtain ⟨_, _, _, _, _, disjoint, targets, below, py⟩ :=
      rankRealization_completion_geometry event.1 hr hp hk hy hn bounds gap before packet
    have len := completeMarkRow_length ((event.1.valid r row hr).1.imp (fun lt => Nat.ne_of_lt lt))
      nodup disjoint (fun x hx => (below x hx).le.trans py) targets
    rw [same, len]
    change _ = _ + 2 * (row.step + sources.length)
    omega

/-- The balance survives every actual frozen prefix, including inactive marks. -/
theorem frozen_fold_length_step_balance {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r : Nat} (frozen : List Nat)
    (events : ∀ done mark suffix, frozen = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row out : Row} (hr : rowAt a r = some row)
    (hout : rowAt (frozen.foldl (fun current z => completeMark current rec r z) a) r = some out) :
    out.core.length + 2 * row.step = row.core.length + 2 * out.step := by
  induction frozen generalizing a row with
  | nil =>
    have same : out = row := Option.some.inj (hout.symm.trans hr)
    simp only [same]
  | cons y rest ih =>
    have rb := rowAt_bounds hr
    obtain ⟨mid, atMid⟩ := rowAt_exists (a := completeMark a rec r y) rb.1
      (by simpa only [completeMark_length] using rb.2)
    have first := completionEvent_length_step_balance (events [] y rest rfl) hr atMid
    have prior : ∀ done mark suffix, rest = done ++ mark :: suffix →
        CompletionEventGeometry
          (done.foldl (fun current z => completeMark current rec r z) (completeMark a rec r y)) rec r mark theta embedding := by
      intro done mark suffix eq
      have result := events (y :: done) mark suffix (by simp only [List.cons_append, eq])
      simpa only [List.foldl_cons] using result
    have later := ih prior atMid (by simpa only [List.foldl_cons] using hout)
    omega

/-- Native eligibility is unchanged by the whole verified frozen completion. -/
theorem completeFrozenMarks_eligible_iff {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r : Nat} {row out : Row} (hr : rowAt a r = some row)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (hout : rowAt (completeFrozenMarks a rec r) r = some out) :
    (out.core.length ≤ 2 * out.step ↔ row.core.length ≤ 2 * row.step) := by
  have balance := frozen_fold_length_step_balance row.marks events hr
    (by simpa only [completeFrozenMarks, hr] using hout)
  omega

end FullMarkedBLP
