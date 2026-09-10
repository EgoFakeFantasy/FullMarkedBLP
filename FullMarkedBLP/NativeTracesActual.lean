import FullMarkedBLP.NativeBlockTraces

namespace FullMarkedBLP

theorem nativeBlock_actual_traces {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (h : nativeSources a r = some sources)
    (hn : native a r = some (b, sources))
    (traces : ∀ y ∈ row.marks, ∃ xs, MarkTrace a r y xs) :
    ∃ block, nativeBlock row r sources = some block ∧ BlockTraces b block := by
  have hv := valid r row hr
  cases sources with
  | nil =>
    refine ⟨[row], rfl, ?_⟩
    intro i hi
    have : i = 0 := by simpa using hi
    subst i
    have he := Option.some.inj (hn.symm.trans (native_empty hr h))
    have hab : b = a := congrArg Prod.fst he
    subst b
    simpa using (row_hasTraces_iff hr).mpr traces
  | cons s ss =>
    have hne : s :: ss ≠ [] := by simp
    have helig := nativeSources_nonempty_eligible hr h hne
    have hstep : 2 ≤ row.step := by
      have hp := hv.2.2.2.1
      by_cases he : row.step = 1
      · have hh := nativeSources_step_one_empty hv hr he
        have := Option.some.inj (h.symm.trans hh)
        contradiction
      · omega
    have htop := nativeTop_actual_coreValid valid hr h
    have htopMarks := nativeTop_actual_properMarks valid hr hm h
    have htraces := (row_hasTraces_iff (native_top_rowAt hr hn hne)).mpr
      (native_top_all_marks_have_trace valid hr hm traces h hn hne)
    have htoplen := nativeTop_actual_length valid hr h
    have ht : ∀ x, r ≤ x → x ≤ r + (s :: ss).length →
        x ∈ (nativeTop row r (s :: ss)).core := by
      intro x hx hb
      apply (nativeTop_core_mem row r (s :: ss) x).mpr
      by_cases he : x = r
      · subst x; exact Or.inl (List.mem_of_getLast? hv.2.2.1)
      · exact Or.inr (Or.inr ⟨by omega, hb⟩)
    by_cases hmedium : row.core.length = 2 * row.step
    · obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_medium_traces ss.length htop htopMarks htraces
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) ht
      exact ⟨block, by simpa [nativeBlock, hmedium] using hb, hvalid⟩
    · have hbool : (row.core.length == 2 * row.step) = false := by
        exact Bool.eq_false_iff.mpr (by simpa using hmedium)
      have hshort : row.core.length + 1 = 2 * row.step := by
        have hs := hv.2.2.2
        unfold Row.OrdinaryShape at hs
        rcases hs with ⟨hp, hs | hs | hs⟩ <;> omega
      have hsmin : 3 ≤ row.step := by
        have hs := hv.2.2.2
        unfold Row.OrdinaryShape at hs
        rcases hs with ⟨hp, hs | hs | hs⟩ <;> omega
      obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_short_traces (s :: ss).length htop htopMarks htraces
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      exact ⟨block, by simpa [nativeBlock, hbool] using hb, hvalid⟩


#print axioms nativeBlock_actual_traces
end FullMarkedBLP


