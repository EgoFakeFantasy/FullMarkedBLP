import FullMarkedBLP.ScanStepBExact

namespace FullMarkedBLP

/-- The bottom B cannot increase under native, also when no block is inserted. -/
theorem native_bottom_b_le_or_empty {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r oldB newB : Nat} {row bottom : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : native a r = some (b, sources))
    (hbottom : rowAt b r = some bottom)
    (hb : row.b = some oldB) (hbnew : bottom.b = some newB) : newB ≤ oldB := by
  exact (Option.some.inj (hbnew.symm.trans
    (native_bottom_b_eq valid hr hn hbottom hb))).le

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
  exact (Option.some.inj (hw.symm.trans
    (scan_step_bottom_b_update h hr hb events hn hbottom))).le

end FullMarkedBLP
