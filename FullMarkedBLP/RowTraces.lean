import FullMarkedBLP.NativeLowerTrace

namespace FullMarkedBLP

/-- Trace witnesses attached to a literal row in a fixed ambient pattern. -/
def Row.HasTraces (a : Pattern) (row : Row) : Prop :=
  ∀ y ∈ row.marks, ∃ k x xs, row.step ≤ k ∧ row.core[k]? = some y ∧
    row.core[k - row.step]? = some x ∧ Trace a x y xs

theorem row_hasTraces_iff {a : Pattern} {r : Nat} {row : Row}
    (hr : rowAt a r = some row) :
    row.HasTraces a ↔ ∀ y ∈ row.marks, ∃ xs, MarkTrace a r y xs := by
  constructor
  · intro ht y hy
    obtain ⟨k, x, xs, hk, hky, hkx, ht⟩ := ht y hy
    exact ⟨xs, row, k, x, hr, hy, hk, hky, hkx, ht⟩
  · intro ht y hy
    obtain ⟨xs, old, k, x, ho, _, hk, hky, hkx, ht⟩ := ht y hy
    have he := Option.some.inj (ho.symm.trans hr)
    subst old
    exact ⟨k, x, xs, hk, hky, hkx, ht⟩

theorem nativeLower_marks_sublist {row lower : Row} {owner : Nat} {medium : Bool}
    (h : nativeLower row owner medium = some lower) :
    List.Sublist lower.marks row.marks := by
  cases medium with
  | true => cases Option.some.inj h; exact List.erase_sublist
  | false =>
    obtain ⟨e, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    exact List.erase_sublist

theorem nativeLower_medium_traces {a : Pattern} {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (ht : row.HasTraces a) (h : nativeLower row owner true = some lower) : lower.HasTraces a := by
  intro y hy
  have hy' := (nativeLower_marks_sublist h).subset hy
  obtain ⟨k, x, xs, hk, hky, hkx, htrace⟩ := ht y hy'
  have hp := nativeLower_medium_pair hv (hm.2 y hy').1 hky hkx h
  have hs := nativeLower_step h
  simp only [↓reduceIte] at hs
  exact ⟨k, x, xs, by omega, hp.1, hp.2, htrace⟩

theorem nativeLower_short_traces {a : Pattern} {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (hlen : row.core.length + 1 = 2 * row.step)
    (ht : row.HasTraces a) (h : nativeLower row owner false = some lower) : lower.HasTraces a := by
  intro y hy
  have hy' := (nativeLower_marks_sublist h).subset hy
  obtain ⟨k, x, xs, hk, hky, hkx, htrace⟩ := ht y hy'
  have hp := nativeLower_short_pair hv hm hlen hy' hk hky hkx h
  have hs := nativeLower_step h
  simp only [Bool.false_eq_true, ↓reduceIte] at hs
  exact ⟨k - 1, x, xs, by omega, hp.1, hp.2, htrace⟩

end FullMarkedBLP
