import FullMarkedBLP.CompletionEventEdges

namespace FullMarkedBLP

/-- Geometrically valid completion preserves e once the mark lies at or above e. -/
theorem completionEvent_preserves_e {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y e : Nat} (event : CompletionEventGeometry a rec r y theta embedding)
    {row out : Row} (hr : rowAt a r = some row) (he : row.e = some e)
    (above : ∀ sources, completionRecord a rec r y = some sources → e ≤ y)
    (hout : rowAt (completeMark a rec r y) r = some out) : out.e = some e := by
  cases hc : completionRecord a rec r y with
  | none =>
    have eq : out = row := by simpa only [completeMark, hr, hc, Option.some.injEq] using hout.symm
    simpa only [eq] using he
  | some sources =>
    obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
      event.2 row sources hr hc
    obtain ⟨left, right, _, _, _, disjoint, targetGap, below, _⟩ :=
      rankRealization_completion_geometry event.1 hr hp hk hy hnext bounds gap beforeOwner packet
    have pe := row_p_lt_e (event.1.valid r row hr) hp he
    have result := completeMarkRow_e (event.1.valid r row hr) he hs disjoint targetGap
      (above sources hc) (fun x hx => (below x hx).trans pe)
    have eq : out = completeMarkRow row y sources := by
      simpa only [completeMark, hr, hc, rowAt_set_self hr, Option.some.injEq] using hout.symm
    simpa only [eq] using result

/-- At an actual scan entrance, prior validity suffices for preservation of e. -/
theorem completionEvent_reachable_preserves_e {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y e : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r)
    (event : CompletionEventGeometry a rec r y theta embedding)
    {row out : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (he : row.e = some e) (hout : rowAt (completeMark a rec r y) r = some out) : out.e = some e := by
  apply completionEvent_preserves_e event hr he _ hout
  intro sources hc
  have valid := event.1.valid r row hr
  have len : 0 < row.core.length := by have := valid.2.1; omega
  have head : row.core.head? = some (row.core[0]'len) := by simp [List.head?_eq_getElem?]
  exact realized_completion_e_le_mark historyValid reach event.1 hr hm head he hc

end FullMarkedBLP
