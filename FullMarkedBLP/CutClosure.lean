import FullMarkedBLP.ScanTotal

namespace FullMarkedBLP

theorem cut_is_prefix {a b : Pattern} (h : cut a = some b) : b <+: a := by
  unfold cut at h
  split at h
  next => cases Option.some.inj h; exact List.dropLast_prefix a
  next => simp at h

theorem cut_preserves_coreValid {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : cut a = some b) : ∀ r row, rowAt b r = some row → row.CoreValid r := by
  intro r row hr
  exact valid r row ((prefix_rowAt (cut_is_prefix h) (rowAt_bounds hr).2).trans hr)

theorem cut_preserves_properMarks {a b : Pattern}
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (h : cut a = some b) : ∀ r row, rowAt b r = some row → row.ProperMarks r := by
  intro r row hr
  exact marks r row ((prefix_rowAt (cut_is_prefix h) (rowAt_bounds hr).2).trans hr)

theorem cut_preserves_traces {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (traces : ∀ r row, rowAt a r = some row → row.HasTraces a)
    (h : cut a = some b) : ∀ r row, rowAt b r = some row → row.HasTraces b := by
  intro r row hr y hy
  have hbound := (rowAt_bounds hr).2
  have ha : rowAt a r = some row := (prefix_rowAt (cut_is_prefix h) hbound).trans hr
  obtain ⟨k, s, xs, hk, hky, hks, ht⟩ := traces r row ha y hy
  have hyr := (marks r row ha).2 y hy
  refine ⟨k, s, xs, hk, hky, hks, ?_⟩
  apply trace_prefix valid ht (show y < b.length + 1 by omega)
  intro i hi
  exact (prefix_rowAt (cut_is_prefix h) (by omega : i ≤ b.length))

theorem cut_preserves_sat {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (h : cut a = some b) : Sat b := by
  intro r row hr heligible
  have hbound := (rowAt_bounds hr).2
  have ha : rowAt a r = some row := (prefix_rowAt (cut_is_prefix h) hbound).trans hr
  obtain ⟨p, e, er, v, hp, he, her, hb, hle⟩ := hs r row ha heligible
  have hv := valid r row ha
  have heBound := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
  exact ⟨p, e, er, v, hp, he, (prefix_rowAt (cut_is_prefix h) (by omega)).symm.trans her, hb, hle⟩

end FullMarkedBLP

