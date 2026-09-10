import FullMarkedBLP.FrozenHistoricalTrace
import FullMarkedBLP.CompletionAllRealizedEdges
import FullMarkedBLP.NativeTopMarks
import FullMarkedBLP.CompletionTargetBound

namespace FullMarkedBLP

/-- All actual completed row edges are preserved once the endpoint condition
is established. For long rows this condition remains a separate obligation. -/
theorem completionEvent_all_edges {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat} (event : CompletionEventGeometry a rec r y theta embedding)
    (endpoint : ∀ row sources, rowAt a r = some row → completionRecord a rec r y = some sources →
      ∃ e, row.e = some e ∧ e ≤ y) :
    ∀ i out, rowAt (completeMark a rec r y) i = some out →
      out.RealizesEdges (rankOrdinalAction (embedding i)) theta i := by
  cases hr : rowAt a r with
  | none => simpa only [completeMark, hr] using event.1.edges
  | some row =>
    cases hc : completionRecord a rec r y with
    | none => simpa only [completeMark, hr, hc] using event.1.edges
    | some sources =>
      obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
        event.2 row sources hr hc
      obtain ⟨e, he, hey⟩ := endpoint row sources hr hc
      have edges := rankRealization_completion_all_edges event.1 hr hp he hey hk hy hnext
        hs bounds gap beforeOwner packet
      intro i out hout
      simp only [completeMark, hr, hc] at hout
      by_cases hi : i = r
      · subst i
        rw [rowAt_set_self hr] at hout
        cases Option.some.inj hout
        exact edges
      · rw [rowAt_set_other hr hi] at hout
        exact event.1.edges i out hout

/-- Short and medium marked rows discharge the endpoint condition directly. -/
theorem completionEvent_eligible_all_edges {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat} (event : CompletionEventGeometry a rec r y theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (eligible : row.core.length ≤ 2 * row.step) :
    ∀ i out, rowAt (completeMark a rec r y) i = some out →
      out.RealizesEdges (rankOrdinalAction (embedding i)) theta i := by
  apply completionEvent_all_edges event
  intro other sources hother _
  have heq := Option.some.inj (hother.symm.trans hr)
  subst other
  have valid := event.1.valid r row hr
  have bound := Row.step_lt_length valid.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) valid.2.2.2.1 (by omega)
  exact ⟨e, he, eligible_source_le_mark valid (event.1.proper r row hr) eligible he hm⟩

/-- At a reachable scan entrance, prior validity discharges the endpoint
condition for every ordinary row, including long rows. -/
theorem completionEvent_reachable_all_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r)
    (event : CompletionEventGeometry a rec r y theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hy : y ∈ row.marks) :
    ∀ i out, rowAt (completeMark a rec r y) i = some out →
      out.RealizesEdges (rankOrdinalAction (embedding i)) theta i := by
  apply completionEvent_all_edges event
  intro other sources hother hc
  have heq := Option.some.inj (hother.symm.trans hr)
  subst other
  have valid := event.1.valid r row hr
  have bound := Row.step_lt_length valid.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) valid.2.2.2.1 (by omega)
  have hlen : 0 < row.core.length := by have := valid.2.1; omega
  let minimum := row.core[0]'hlen
  have hm : row.core.head? = some minimum := by simp [List.head?_eq_getElem?, minimum]
  exact ⟨e, he, realized_completion_e_le_mark historyValid reach event.1 hr hy hm he hc⟩
/-- Every intermediate frozen event has all-edge preservation, including long
rows, when its current event geometry and marked membership are established. -/
theorem completionEvent_frozen_prefix_all_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (processed : List Nat)
    (event : CompletionEventGeometry
      (processed.foldl (fun current mark => completeMark current rec r mark) a) rec r y theta embedding)
    {row : Row}
    (hr : rowAt (processed.foldl (fun current mark => completeMark current rec r mark) a) r = some row)
    (hy : y ∈ row.marks) :
    ∀ i out, rowAt (completeMark
      (processed.foldl (fun current mark => completeMark current rec r mark) a) rec r y) i = some out →
      out.RealizesEdges (rankOrdinalAction (embedding i)) theta i := by
  apply completionEvent_all_edges event
  intro other sources hother hc
  have heq := Option.some.inj (hother.symm.trans hr)
  subst other
  have valid := event.1.valid r row hr
  have bound := Row.step_lt_length valid.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) valid.2.2.2.1 (by omega)
  have hlen : 0 < row.core.length := by have := valid.2.1; omega
  let minimum := row.core[0]'hlen
  have hm : row.core.head? = some minimum := by simp [List.head?_eq_getElem?, minimum]
  obtain ⟨k, source, xs, hk, hky, hks, _, hs⟩ :=
    realized_completion_source_above_minimum_frozen_prefix historyValid reach processed event.1 hr hy hm hc
  exact ⟨e, he, target_after_e_of_source_above_minimum valid hm hk hky hks hs he⟩

end FullMarkedBLP



