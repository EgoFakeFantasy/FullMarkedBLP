import FullMarkedBLP.NativeBlockMarks

namespace FullMarkedBLP

theorem nativeBlock_actual_marks {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (h : nativeSources a r = some sources) :
    ∃ block, nativeBlock row r sources = some block ∧ BlockProperMarks r block := by
  have hv := valid r row hr
  cases sources with
  | nil =>
    refine ⟨[row], rfl, ?_⟩
    intro i hi
    have : i = 0 := by simpa using hi
    subst i
    simpa using hm
  | cons s ss =>
    have hne : s :: ss ≠ [] := by simp
    have helig := nativeSources_nonempty_eligible hr h hne
    have hstep := nativeSources_nonempty_step_ge_two hv hr h hne
    have htop := nativeTop_actual_coreValid valid hr h
    have htopMarks := nativeTop_actual_properMarks valid hr hm h
    have htoplen := nativeTop_actual_length valid hr h
    have ht := nativeTop_contains_targets hv (s :: ss)
    by_cases hmedium : row.core.length = 2 * row.step
    · obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_medium_marks ss.length htop htopMarks
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) ht
      exact ⟨block, by simpa [nativeBlock, hmedium] using hb, hvalid⟩
    · have hbool : (row.core.length == 2 * row.step) = false := by
        exact Bool.eq_false_iff.mpr (by simpa using hmedium)
      obtain ⟨hshort, hsmin⟩ := Row.short_shape_of_eligible_ne_medium hv.2.2.2 helig hmedium
      obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_short_marks (s :: ss).length htop htopMarks
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      exact ⟨block, by simpa [nativeBlock, hbool] using hb, hvalid⟩


end FullMarkedBLP
