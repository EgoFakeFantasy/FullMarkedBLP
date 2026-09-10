import FullMarkedBLP.CompletionPreservesEndpoint
import FullMarkedBLP.FrozenPrefixInduction

namespace FullMarkedBLP

/-- The endpoint is preserved at a genuine intermediate frozen event. -/
theorem completionEvent_frozen_preserves_e {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y e : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (processed : List Nat)
    (event : CompletionEventGeometry
      (processed.foldl (fun current mark => completeMark current rec r mark) a) rec r y theta embedding)
    {row out : Row}
    (hr : rowAt (processed.foldl (fun current mark => completeMark current rec r mark) a) r = some row)
    (hm : y ∈ row.marks) (he : row.e = some e)
    (hout : rowAt (completeMark
      (processed.foldl (fun current mark => completeMark current rec r mark) a) rec r y) r = some out) :
    out.e = some e := by
  apply completionEvent_preserves_e event hr he _ hout
  intro sources hc
  have valid := event.1.valid r row hr
  have len : 0 < row.core.length := by have := valid.2.1; omega
  have head : row.core.head? = some (row.core[0]'len) := by simp [List.head?_eq_getElem?]
  obtain ⟨k, source, xs, hk, hy, hs, _, low⟩ :=
    realized_completion_source_above_minimum_frozen_prefix historyValid reach processed event.1 hr hm head hc
  exact target_after_e_of_source_above_minimum valid head hk hy hs low he

/-- All original frozen marks together preserve their owner's entrance endpoint. -/
theorem completeFrozenMarks_preserves_e {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r e : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (h : RankRowRealization a theta embedding)
    {row out : Row} (hr : rowAt a r = some row) (he : row.e = some e)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (hout : rowAt (completeFrozenMarks a rec r) r = some out) : out.e = some e := by
  let P := fun (done : List Nat) (mark : Nat) => CompletionEventGeometry
    (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding
  let Q := fun (done : List Nat) => ∀ rw, rowAt (done.foldl (fun current y => completeMark current rec r y) a) r = some rw →
    rw.e = some e
  have start : Q [] := by
    intro rw atRow
    have eq : rw = row := Option.some.inj (atRow.symm.trans hr)
    simpa only [eq] using he
  have result := frozen_prefix_bootstrap (P := P) (Q := Q) row.marks start (by
    intro done y suffix splitMarks state prior
    have event := events done y suffix splitMarks
    refine ⟨event, ?_⟩
    intro next atNext
    have mem : y ∈ row.marks := by rw [splitMarks]; simp
    obtain ⟨k, source, xs, delta, hk, hy, hs, trace, _, _⟩ := h.marked r row y hr mem
    have old : MarkTrace a r y xs := ⟨row, k, source, hr, mem, hk, hy, hs, trace⟩
    have transported := frozen_fold_preserves_historical_trace done prior old
    obtain ⟨mid, _, _, atMid, marked, _, _, _, _⟩ := transported
    apply completionEvent_frozen_preserves_e historyValid reach done event atMid marked (state mid atMid)
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using atNext)
  apply result.1 out
  simpa only [completeFrozenMarks, hr] using hout

end FullMarkedBLP

