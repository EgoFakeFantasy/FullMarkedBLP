import FullMarkedBLP.FrozenPreservesEndpoint
import FullMarkedBLP.NativeUnexpandedEndpoint

namespace FullMarkedBLP

/-- One actual scan step transports e of every old row except a nonempty expanded owner. -/
theorem scan_step_unexpanded_endpoint {lambda : Ordinal.{u}} {initial a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r i e : Nat} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ j rw, rowAt (completeFrozenMarks before history owner) j = some rw → rw.CoreValid j)
    (reach : ScanReach initial a rec r) (h : RankRowRealization a theta embedding)
    {owner row : Row} (ownerAt : rowAt a r = some owner) (hr : rowAt a i = some row)
    (he : row.e = some e)
    (events : ∀ done mark suffix, owner.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (birth : native (completeFrozenMarks a rec r) r = some (b, sources))
    (unexpanded : i ≠ r ∨ sources = []) :
    (rowAt b (shiftAfter r sources.length i)).bind Row.e =
      some (shiftAfter r sources.length e) := by
  have bounds := rowAt_bounds hr
  obtain ⟨mid, atMid⟩ := rowAt_exists (a := completeFrozenMarks a rec r) bounds.1
    (by simpa only [completeFrozenMarks_length] using bounds.2)
  have midE : mid.e = some e := by
    by_cases eq : i = r
    · subst i
      have rows : row = owner := Option.some.inj (hr.symm.trans ownerAt)
      subst row
      exact completeFrozenMarks_preserves_e historyValid reach h ownerAt he events atMid
    · have fixed := completeFrozenMarks_other_row (a := a) (rec := rec) eq
      have rows : mid = row := Option.some.inj (atMid.symm.trans (fixed.trans hr))
      simpa only [rows] using he
  have valid := (completeFrozenMarks_event_geometry ownerAt h.valid events).1
  exact native_unexpanded_endpoint_shift valid birth atMid midE unexpanded

end FullMarkedBLP
