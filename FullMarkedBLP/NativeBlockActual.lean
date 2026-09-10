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

/-- A nonempty source walk rules out step one: at that step the native
operation has no source to insert. -/
theorem nativeSources_nonempty_step_ge_two {a : Pattern} {r : Nat} {row : Row}
    {sources : List Nat} (hValid : row.CoreValid r) (hRow : rowAt a r = some row)
    (hSources : nativeSources a r = some sources) (hNonempty : sources ≠ []) :
    2 ≤ row.step := by
  have positive := hValid.2.2.2.1
  by_cases one : row.step = 1
  · exact False.elim (hNonempty (Option.some.inj
      (hSources.symm.trans (nativeSources_step_one_empty hValid hRow one))))
  · omega

/-- The native top contains every target from the old owner through the new
owner; these are the consecutive targets used by each block induction. -/
theorem nativeTop_contains_targets {row : Row} {r : Nat} (hValid : row.CoreValid r)
    (sources : List Nat) :
    ∀ x, r ≤ x → x ≤ r + sources.length → x ∈ (nativeTop row r sources).core := by
  intro x lower upper
  apply (nativeTop_core_mem row r sources x).mpr
  by_cases same : x = r
  · subst x
    exact Or.inl (List.mem_of_getLast? hValid.2.2.1)
  · exact Or.inr (Or.inr ⟨by omega, upper⟩)

/-- For an eligible ordinary row outside the medium case, both the short
length equation and its minimum step follow from the same shape analysis. -/
theorem Row.short_shape_of_eligible_ne_medium {row : Row} (hShape : row.OrdinaryShape)
    (hEligible : row.core.length ≤ 2 * row.step)
    (hMedium : row.core.length ≠ 2 * row.step) :
    row.core.length + 1 = 2 * row.step ∧ 3 ≤ row.step := by
  rcases hShape with ⟨positive, shape | shape | shape⟩ <;> omega

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
    have hstep := nativeSources_nonempty_step_ge_two hv hr h hne
    have htop := nativeTop_actual_coreValid valid hr h
    have htoplen := nativeTop_actual_length valid hr h
    have ht := nativeTop_contains_targets hv (s :: ss)
    by_cases hmedium : row.core.length = 2 * row.step
    · obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_medium_total ss.length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) ht
      exact ⟨block, by simpa [nativeBlock, hmedium] using hb, hvalid⟩
    · have hbool : (row.core.length == 2 * row.step) = false := by
        exact Bool.eq_false_iff.mpr (by simpa using hmedium)
      obtain ⟨hshort, hsmin⟩ := Row.short_shape_of_eligible_ne_medium hv.2.2.2 helig hmedium
      obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_short_total (s :: ss).length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      exact ⟨block, by simpa [nativeBlock, hbool] using hb, hvalid⟩


theorem native_total {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} (hr : rowAt a r = some row) :
    ∃ b sources, native a r = some (b, sources) := by
  obtain ⟨sources, hs⟩ := nativeSources_total valid hr
  obtain ⟨block, hb, _⟩ := nativeBlock_actual_total valid hr hs
  refine ⟨a.take (r - 1) ++ block ++ (a.drop r).map (Row.shiftAfter r sources.length), sources, ?_⟩
  simp [native, hr, hs, hb]

end FullMarkedBLP
