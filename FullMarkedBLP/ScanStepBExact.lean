import FullMarkedBLP.NativeBottomBExact
import FullMarkedBLP.FrozenEndpointUpdate

namespace FullMarkedBLP

/-- A whole scan step changes bottom B only by the entrance endpoint completion;
native contributes no further change. -/
theorem scan_step_bottom_b_update {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r v : Nat} {sources : List Nat}
    (h : RankRowRealization a theta embedding)
    {row bottom : Row} (hr : rowAt a r = some row) (hb : row.b = some v)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (birth : native (completeFrozenMarks a rec r) r = some (b, sources))
    (atBottom : rowAt b r = some bottom) :
    bottom.b = some (v + if v ∈ row.marks then
      ((completionRecord a rec r v).getD []).length else 0) := by
  obtain ⟨mid, atMid, _⟩ := Option.bind_eq_some_iff.mp birth
  have valid := (completeFrozenMarks_event_geometry hr h.valid events).1
  exact native_bottom_b_eq valid atMid birth atBottom
    (completeFrozenMarks_b_update h hr hb events atMid)

end FullMarkedBLP
