import FullMarkedBLP.AuxiliaryTotal

namespace FullMarkedBLP

theorem classify_expand_last {a : Pattern}
    (h : classify a = .successor ∨ classify a = .limit) :
    ∃ row, a.getLast? = some row ∧ 4 ≤ row.core.length := by
  unfold classify at h
  split at h
  next => simp at h
  next =>
    cases hl : a.getLast? with
    | none => simp [hl] at h
    | some row =>
      refine ⟨row, rfl, ?_⟩
      simp only [hl] at h
      split at h
      next hs => omega
      next =>
        split at h
        next hs => omega
        next => simp at h

theorem coreValid_expansion_bounds {row : Row} {n : Nat}
    (hv : row.CoreValid n) (hm : 4 ≤ row.core.length) :
    ∃ anchor, row.b = some anchor ∧ 0 < anchor ∧ anchor ≤ n - 1 ∧ 2 < n := by
  obtain ⟨anchor, hb⟩ := Row.b_exists hv
  have hbi := hb
  simp only [Row.b, fromRight, show 0 < (2 : Nat) ∧ 2 ≤ row.core.length by omega] at hbi
  obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp hbi
  have hl := hv.2.2.1
  rw [List.getLast?_eq_getElem?] at hl
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hl
  have hpos := sorted_index_spacing hv.1 0 (row.core.length - 2) (by omega) (by omega)
  have hlt := List.pairwise_iff_getElem.mp hv.1 (row.core.length - 2)
    (row.core.length - 1) hi hj (by omega)
  simp only [Nat.zero_add, hiv] at hpos
  rw [hiv, hjv] at hlt
  exact ⟨anchor, hb, by omega, by omega, by omega⟩

theorem expand_total_coreValid {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (kind : classify a = .successor ∨ classify a = .limit) (k : Nat) :
    ∃ b, expand a k = some b ∧ (∀ r row, rowAt b r = some row → row.CoreValid r) := by
  obtain ⟨row, hl, hm⟩ := classify_expand_last kind
  have hlast := hl
  rw [List.getLast?_eq_getElem?] at hlast
  obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp hlast
  have hn : 0 < a.length := by omega
  have hr : rowAt a a.length = some row := by
    simpa [rowAt, Nat.ne_of_gt hn] using hlast
  obtain ⟨anchor, hb, ha, hab, hsize⟩ := coreValid_expansion_bounds (valid _ _ hr) hm
  have hcut : cut a = some a.dropLast := by simp [cut, hsize]
  obtain ⟨b, he, hv⟩ := expandFrom_total_coreValid (cut_preserves_coreValid valid hcut)
    ha (by simpa using hab) (by simp; omega) k
  refine ⟨b, ?_, hv⟩
  simp [expand, kind, hl, hb, hcut, he]

theorem expand_preserves_marks_traces {a b : Pattern} {k : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (traces : ∀ r row, rowAt a r = some row → row.HasTraces a)
    (h : expand a k = some b) :
    (∀ r row, rowAt b r = some row → row.CoreValid r) ∧
    (∀ r row, rowAt b r = some row → row.ProperMarks r) ∧
    (∀ r row, rowAt b r = some row → row.HasTraces b) := by
  unfold expand at h
  split at h
  next kind =>
    obtain ⟨row, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨anchor, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨initial, hc, he⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨last, hlast, hm⟩ := classify_expand_last kind
    have heq : last = row := Option.some.inj (hlast.symm.trans hl)
    subst last
    have hli := hl
    rw [List.getLast?_eq_getElem?] at hli
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hli
    have hr : rowAt a a.length = some row := by
      simpa [rowAt, show a.length ≠ 0 by omega] using hli
    obtain ⟨anch, hanch, _, hab, hsize⟩ := coreValid_expansion_bounds (valid _ _ hr) hm
    have hae : anch = anchor := Option.some.inj (hanch.symm.trans hb)
    subst anch
    have hic : initial = a.dropLast := by simpa [cut, hsize] using hc.symm
    have hbound : anchor ≤ initial.length := by simp [hic]; exact hab
    exact expandFrom_preserves_marks_traces (cut_preserves_coreValid valid hc)
      (cut_preserves_properMarks marks hc) (cut_preserves_traces valid marks traces hc) hbound he
  next => simp at h

end FullMarkedBLP


