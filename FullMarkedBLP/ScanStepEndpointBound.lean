import FullMarkedBLP.FrozenEndpointUpdate

namespace FullMarkedBLP

/-- The bottom B cannot increase under native, also when no block is inserted. -/
theorem native_bottom_b_le_or_empty {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r oldB newB : Nat} {row bottom : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : native a r = some (b, sources))
    (hbottom : rowAt b r = some bottom)
    (hb : row.b = some oldB) (hbnew : bottom.b = some newB) : newB ≤ oldB := by
  by_cases empty : sources = []
  · subst sources
    have same := native_empty hr (native_sources_of_success hn)
    have ab : b = a := (Prod.mk.inj (Option.some.inj (hn.symm.trans same))).1
    subst b
    have rows : bottom = row := Option.some.inj (hbottom.symm.trans hr)
    subst bottom
    have eq := Option.some.inj (hbnew.symm.trans hb)
    omega
  · exact native_bottom_b_le valid hr hn empty hbottom hb hbnew

/-- Actual compTo followed by native has an entrance-record bound on bottom B. -/
theorem scan_step_bottom_b_bound {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r v w : Nat} {sources : List Nat}
    (h : RankRowRealization a theta embedding)
    {row bottom : Row} (hr : rowAt a r = some row) (hb : row.b = some v)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (hn : native (completeFrozenMarks a rec r) r = some (b, sources))
    (hbottom : rowAt b r = some bottom) (hw : bottom.b = some w) :
    w ≤ v + if v ∈ row.marks then ((completionRecord a rec r v).getD []).length else 0 := by
  have valid := (completeFrozenMarks_event_geometry hr h.valid events).1
  have bounds := rowAt_bounds hr
  obtain ⟨mid, atMid⟩ := rowAt_exists (a := completeFrozenMarks a rec r) bounds.1 (by
    simpa only [completeFrozenMarks, hr, completeMarks_fold_length] using bounds.2)
  have midB := completeFrozenMarks_b_update h hr hb events atMid
  exact native_bottom_b_le_or_empty valid atMid hn hbottom midB hw

end FullMarkedBLP
