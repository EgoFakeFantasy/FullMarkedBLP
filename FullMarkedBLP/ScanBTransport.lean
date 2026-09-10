import FullMarkedBLP.NativeBTransport
import FullMarkedBLP.FrozenEndpointUpdate

namespace FullMarkedBLP

/-- Every old B follows the native column map, with precisely the owner's
endpoint-completion increment added before that map. -/
theorem scan_step_all_b_update {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r i v : Nat} {sources : List Nat}
    (h : RankRowRealization a theta embedding)
    {owner row : Row} (ownerAt : rowAt a r = some owner)
    (hr : rowAt a i = some row) (hb : row.b = some v)
    (events : ∀ done mark suffix, owner.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (birth : native (completeFrozenMarks a rec r) r = some (b, sources)) :
    (rowAt b (shiftAfter r sources.length i)).bind Row.b =
      some (shiftAfter r sources.length (v + if i = r ∧ v ∈ row.marks then
        ((completionRecord a rec r v).getD []).length else 0)) := by
  have valid := (completeFrozenMarks_event_geometry ownerAt h.valid events).1
  by_cases eq : i = r
  · subst i
    have same : row = owner := Option.some.inj (hr.symm.trans ownerAt)
    subst row
    obtain ⟨mid, atMid, _⟩ := Option.bind_eq_some_iff.mp birth
    have endpoint := completeFrozenMarks_b_update h ownerAt hb events atMid
    simpa only [true_and, eq_self] using native_b_shift valid birth atMid endpoint
  · have atMid : rowAt (completeFrozenMarks a rec r) i = some row :=
      (completeFrozenMarks_other_row eq).trans hr
    simpa only [eq, false_and, if_false, Nat.add_zero] using native_b_shift valid birth atMid hb

end FullMarkedBLP
