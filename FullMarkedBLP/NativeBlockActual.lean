import FullMarkedBLP.NativeBlock

namespace FullMarkedBLP

theorem nativeSources_step_one_empty {a : Pattern} {r : Nat} {row : Row}
    (hv : row.CoreValid r) (hr : rowAt a r = some row) (hstep : row.step = 1) :
    nativeSources a r = some [] := by
  by_cases hlong : 2 * row.step < row.core.length
  · simp [nativeSources, hr, hlong]
  · have hm : row.core.length = 2 := by have := hv.2.1; omega
    obtain ⟨p, hp⟩ := Row.b_exists hv
    have he : row.e = some r := by
      simpa [Row.e, fromRight, hstep, hm, List.getLast?_eq_getElem?] using hv.2.2.1
    have hp' : row.p = some p := by simpa [Row.p, Row.b, hstep] using hp
    simp [nativeSources, hr, hlong, hp', he, nativeSourcesFuel, hp]

theorem nativeSources_nonempty_eligible {a : Pattern} {r : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row)
    (h : nativeSources a r = some sources) (hne : sources ≠ []) :
    row.core.length ≤ 2 * row.step := by
  by_cases hh : 2 * row.step < row.core.length
  · have he : nativeSources a r = some [] := by simp [nativeSources, hr, hh]
    have := Option.some.inj (h.symm.trans he)
    contradiction
  · omega

/-- Actual native block is total and every row has its correct indexed core. -/
theorem nativeBlock_actual_total {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources) :
    ∃ block, nativeBlock row r sources = some block ∧ BlockCoreValid r block := by
  have hv := valid r row hr
  cases sources with
  | nil =>
    refine ⟨[row], rfl, ?_⟩
    intro i hi
    have : i = 0 := by simpa using hi
    subst i
    simpa using hv
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
    have htoplen := nativeTop_actual_length valid hr h
    have ht : ∀ x, r ≤ x → x ≤ r + (s :: ss).length →
        x ∈ (nativeTop row r (s :: ss)).core := by
      intro x hx hb
      apply (nativeTop_core_mem row r (s :: ss) x).mpr
      by_cases he : x = r
      · subst x; exact Or.inl (List.mem_of_getLast? hv.2.2.1)
      · exact Or.inr (Or.inr ⟨by omega, hb⟩)
    by_cases hmedium : row.core.length = 2 * row.step
    · obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_medium_total ss.length htop
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
      obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_short_total (s :: ss).length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      exact ⟨block, by simpa [nativeBlock, hbool] using hb, hvalid⟩

#print axioms nativeBlock_actual_total




theorem native_total {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} (hr : rowAt a r = some row) :
    ∃ b sources, native a r = some (b, sources) := by
  obtain ⟨sources, hs⟩ := nativeSources_total valid hr
  obtain ⟨block, hb, _⟩ := nativeBlock_actual_total valid hr hs
  refine ⟨a.take (r - 1) ++ block ++ (a.drop r).map (Row.shiftAfter r sources.length), sources, ?_⟩
  simp [native, hr, hs, hb]

#print axioms native_total
end FullMarkedBLP
