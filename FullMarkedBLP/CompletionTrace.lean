import FullMarkedBLP.CompletionRank

namespace FullMarkedBLP

theorem rowAt_set_self {a : Pattern} {r : Nat} {old new : Row}
    (hr : rowAt a r = some old) : rowAt (a.set (r - 1) new) r = some new := by
  have hb := rowAt_bounds hr
  simp [rowAt, show r ≠ 0 by omega, show r - 1 < a.length by omega]

theorem rowAt_set_other {a : Pattern} {r i : Nat} {old new : Row}
    (hr : rowAt a r = some old) (hi : i ≠ r) :
    rowAt (a.set (r - 1) new) i = rowAt a i := by
  have hb := rowAt_bounds hr
  by_cases hz : i = 0
  · subst i; simp [rowAt]
  · simp [rowAt, hz, List.getElem?_set_ne (show r - 1 ≠ i - 1 by omega)]

theorem predecessor_set_eq {a : Pattern} {r : Nat} {old new : Row}
    (hr : rowAt a r = some old) (hp : new.p = old.p) :
    ∀ i, predecessor (a.set (r - 1) new) i = predecessor a i := by
  intro i
  by_cases hi : i = r
  · subst i; simp only [predecessor, rowAt_set_self hr, hr, Option.bind_some, hp]
  · simp only [predecessor, rowAt_set_other hr hi]

theorem trace_of_predecessor_eq {a b : Pattern}
    (he : ∀ i, predecessor b i = predecessor a i)
    {s y : Nat} {xs : List Nat} (ht : Trace a s y xs) : Trace b s y xs := by
  induction ht with
  | stop => exact Trace.stop
  | next hlt hp ht ih => exact Trace.next hlt (by simpa only [he] using hp) ih

theorem trace_iff_of_predecessor_eq {a b : Pattern}
    (he : ∀ i, predecessor b i = predecessor a i) {s y : Nat} {xs : List Nat} :
    Trace b s y xs ↔ Trace a s y xs :=
  ⟨trace_of_predecessor_eq (fun i => (he i).symm), trace_of_predecessor_eq he⟩

/-- Completion preserves exactly the old unmarked chains under its gap hypotheses. -/
theorem completion_trace_iff {a : Pattern} {r y p : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hv : row.CoreValid r) (hp : row.p = some p)
    (hs : sources.Nodup) (hdis : ∀ z ∈ sources, z ∉ row.core)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hpy : p ≤ y) (hbelow : ∀ z ∈ sources, z < p)
    {s x : Nat} {xs : List Nat} :
    Trace (a.set (r - 1) (completeMarkRow row y sources)) s x xs ↔ Trace a s x xs := by
  have he := completeMarkRow_p hv hp hs hdis ht hpy hbelow
  exact trace_iff_of_predecessor_eq (predecessor_set_eq hr (he.trans hp.symm))

theorem markTrace_set_other_iff {a : Pattern} {r owner y : Nat} {old new : Row}
    {xs : List Nat} (hr : rowAt a r = some old) (hp : new.p = old.p)
    (ho : owner ≠ r) :
    MarkTrace (a.set (r - 1) new) owner y xs ↔ MarkTrace a owner y xs := by
  have he := predecessor_set_eq hr hp
  constructor
  · rintro ⟨row, k, s, hrow, hm, hk, hky, hks, ht⟩
    refine ⟨row, k, s, ?_, hm, hk, hky, hks, (trace_iff_of_predecessor_eq he).mp ht⟩
    simpa only [rowAt_set_other hr ho] using hrow
  · rintro ⟨row, k, s, hrow, hm, hk, hky, hks, ht⟩
    refine ⟨row, k, s, ?_, hm, hk, hky, hks, (trace_iff_of_predecessor_eq he).mpr ht⟩
    simpa only [rowAt_set_other hr ho] using hrow

end FullMarkedBLP

