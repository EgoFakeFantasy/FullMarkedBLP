import FullMarkedBLP.CompletionRowClosure

namespace FullMarkedBLP

/-- Replacing one row preserves any row-local invariant verified on the replacement. -/
theorem rowProperty_set {a : Pattern} {r : Nat} {old new : Row} {P : Nat → Row → Prop}
    (ha : ∀ i row, rowAt a i = some row → P i row)
    (hr : rowAt a r = some old) (hnew : P r new) :
    ∀ i row, rowAt (a.set (r - 1) new) i = some row → P i row := by
  intro i row hi
  by_cases he : i = r
  · subst i
    rw [rowAt_set_self hr] at hi
    cases Option.some.inj hi
    exact hnew
  · apply ha i row
    simpa only [rowAt_set_other hr he] using hi

theorem rowTraces_set {a : Pattern} {r : Nat} {old new : Row}
    (ha : ∀ i row, rowAt a i = some row → row.HasTraces a)
    (hr : rowAt a r = some old) (hp : new.p = old.p)
    (hnew : new.HasTraces (a.set (r - 1) new)) :
    ∀ i row, rowAt (a.set (r - 1) new) i = some row → row.HasTraces (a.set (r - 1) new) := by
  intro i row hi
  by_cases he : i = r
  · subst i
    rw [rowAt_set_self hr] at hi
    cases Option.some.inj hi
    exact hnew
  · have ho : rowAt a i = some row := by simpa only [rowAt_set_other hr he] using hi
    apply (row_hasTraces_iff hi).mpr
    intro y hy
    obtain ⟨xs, ht⟩ := (row_hasTraces_iff ho).mp (ha i row ho) y hy
    exact ⟨xs, (markTrace_set_other_iff hr hp he).mpr ht⟩

theorem completion_pattern_hasTraces {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y k left right p : Nat} {row : Row} {sources : List Nat}
    (hrow : rowAt a r = some row) (hm : row.ProperMarks r)
    (oldTraces : ∀ i old, rowAt a i = some old → old.HasTraces a) (hp : row.p = some p) (hpy : p ≤ y)
    (hbelowp : ∀ x ∈ sources, x < p) (hs : sources.Nodup)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hl : row.core[k - row.step]? = some left)
    (hr : row.core[k - row.step + 1]? = some right)
    (hgap : ∀ z ∈ sources, left < z ∧ z < right)
    (hst : ∀ z ∈ sources, z < y)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hbound : y + sources.length < r)
    (intervals : ∀ z ∈ row.marks, ∀ i x, row.step ≤ i →
      row.core[i]? = some z → row.core[i - row.step]? = some x →
      (x ≤ z ∧ z ≤ y ∧ ∀ w ∈ sources, x < w ∧ w < z) ∨
      (x ≤ y ∧ y + sources.length < z ∧ ∀ w ∈ sources, w < x))
    (packet : ∀ x ∈ sources, ∃ xs, Trace a x (y + ((sources.filter (· < x)).length + 1)) xs) :
    ∀ i target, rowAt (a.set (r - 1) (completeMarkRow row y sources)) i = some target →
      target.HasTraces (a.set (r - 1) (completeMarkRow row y sources)) := by
  have hdis : ∀ x ∈ sources, x ∉ row.core := by
    intro x hx
    exact between_adjacent_not_mem (valid r row hrow).1 hl hr (hgap x hx).1 (hgap x hx).2
  have he := completeMarkRow_p (valid r row hrow) hp hs hdis ht hpy hbelowp
  apply rowTraces_set oldTraces hrow (he.trans hp.symm)
  exact completion_row_hasTraces valid hrow hm (oldTraces r row hrow) hs hk hy hl hr
    hgap hst ht hbound intervals packet

end FullMarkedBLP

