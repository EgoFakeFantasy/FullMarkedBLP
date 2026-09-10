import FullMarkedBLP.ScanPrefix

namespace FullMarkedBLP

/-- Future marked source positions remain the same during completion, while
its verified predecessor preservation retains the entire exact trace. -/
theorem frozen_future_markTrace {a : Pattern} {rec : Records} {cursor owner y : Nat}
    {xs : List Nat}
    (preserves : ∀ i, predecessor (completeFrozenMarks a rec cursor) i = predecessor a i)
    (ho : owner ≠ cursor) (ht : MarkTrace a owner y xs) :
    MarkTrace (completeFrozenMarks a rec cursor) owner y xs := by
  obtain ⟨row, k, s, hr, hm, hk, hy, hs, trace⟩ := ht
  refine ⟨row, k, s, ?_, hm, hk, hy, hs, ?_⟩
  · rw [completeFrozenMarks_other_row ho]
    exact hr
  · exact (trace_iff_of_predecessor_eq preserves).mpr trace

/-- A whole actual scan step transports future marked words and their source
positions by the same native insertion map. -/
theorem scan_step_future_markTrace {a b : Pattern} {rec : Records}
    {cursor owner y : Nat} {sources xs : List Nat}
    (valid : ∀ i row, rowAt (completeFrozenMarks a rec cursor) i = some row → row.CoreValid i)
    (preserves : ∀ i, predecessor (completeFrozenMarks a rec cursor) i = predecessor a i)
    (hn : native (completeFrozenMarks a rec cursor) cursor = some (b, sources))
    (ho : cursor < owner) (ht : MarkTrace a owner y xs) :
    MarkTrace b (owner + sources.length) (shiftAfter cursor sources.length y)
      (xs.map (shiftAfter cursor sources.length)) := by
  exact native_suffix_markTrace valid hn
    (frozen_future_markTrace preserves (by omega) ht) ho

end FullMarkedBLP
