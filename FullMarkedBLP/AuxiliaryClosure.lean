import FullMarkedBLP.CutClosure

namespace FullMarkedBLP

theorem auxiliary_row_coreValid {anchor n : Nat} (h : anchor ≤ n) :
    (⟨[anchor, n + 1], 1, []⟩ : Row).CoreValid (n + 1) := by
  simp [Row.CoreValid, Row.OrdinaryShape, show anchor < n + 1 by omega]

theorem auxiliary_append_coreValid {a : Pattern} {anchor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r) (ha : anchor ≤ a.length) :
    ∀ r row, rowAt (a ++ [⟨[anchor, a.length + 1], 1, []⟩]) r = some row → row.CoreValid r := by
  apply coreValid_iff_block.mpr
  apply blockCoreValid_append (coreValid_iff_block.mp valid)
  intro i hi
  have he : i = 0 := by simpa using hi
  subst i
  simpa [Nat.add_comm] using auxiliary_row_coreValid ha

theorem auxiliary_append_properMarks {a : Pattern} {anchor : Nat}
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r) :
    ∀ r row, rowAt (a ++ [⟨[anchor, a.length + 1], 1, []⟩]) r = some row → row.ProperMarks r := by
  apply properMarks_iff_block.mpr
  apply blockProperMarks_append (properMarks_iff_block.mp marks)
  intro i hi
  have he : i = 0 := by simpa using hi
  subst i
  simp [Row.ProperMarks]

theorem auxiliaryStep_preserves_coreValid {a b : Pattern} {anchor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r) (ha : anchor ≤ a.length)
    (h : auxiliaryStep anchor a = some b) :
    ∀ r row, rowAt b r = some row → row.CoreValid r :=
  shortCopy_preserves_coreValid (auxiliary_append_coreValid valid ha) h

theorem auxiliaryStep_preserves_properMarks {a b : Pattern} {anchor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r) (ha : anchor ≤ a.length)
    (h : auxiliaryStep anchor a = some b) :
    ∀ r row, rowAt b r = some row → row.ProperMarks r :=
  shortCopy_preserves_properMarks (auxiliary_append_coreValid valid ha) (auxiliary_append_properMarks marks) h

theorem auxiliary_append_traces {a : Pattern} {anchor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (traces : ∀ r row, rowAt a r = some row → row.HasTraces a) :
    ∀ r row, rowAt (a ++ [⟨[anchor, a.length + 1], 1, []⟩]) r = some row →
      row.HasTraces (a ++ [⟨[anchor, a.length + 1], 1, []⟩]) := by
  intro r row hr
  by_cases hbefore : r ≤ a.length
  · have hpre : a <+: a ++ [⟨[anchor, a.length + 1], 1, []⟩] := List.prefix_append _ _
    have ha : rowAt a r = some row := (prefix_rowAt hpre hbefore).symm.trans hr
    intro y hy
    obtain ⟨k, s, xs, hk, hky, hks, ht⟩ := traces r row ha y hy
    have hyr := (marks r row ha).2 y hy
    refine ⟨k, s, xs, hk, hky, hks, ?_⟩
    exact trace_prefix valid ht (show y < a.length + 1 by omega)
      (fun i hi => (prefix_rowAt hpre (by omega)).symm)
  · have hb := rowAt_bounds hr
    have heq : r = a.length + 1 := by simp only [List.length_append, List.length_singleton] at hb; omega
    subst r
    have hrow : row = ⟨[anchor, a.length + 1], 1, []⟩ := by
      simpa [rowAt, List.getElem?_append_right (Nat.le_refl a.length)] using hr.symm
    subst row
    intro y hy
    simp at hy

theorem auxiliaryStep_preserves_traces {a b : Pattern} {anchor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (traces : ∀ r row, rowAt a r = some row → row.HasTraces a)
    (ha : anchor ≤ a.length) (h : auxiliaryStep anchor a = some b) :
    ∀ r row, rowAt b r = some row → row.HasTraces b :=
  shortCopy_preserves_traces (auxiliary_append_coreValid valid ha) (auxiliary_append_properMarks marks)
    (auxiliary_append_traces valid marks traces) h

end FullMarkedBLP

