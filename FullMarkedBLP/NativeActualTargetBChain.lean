import FullMarkedBLP.NativeMediumTargetBChain

namespace FullMarkedBLP

theorem nativeBlock_actual_target_b {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    (hne : sources ≠ []) (hb : nativeBlock row r sources = some block) :
    ∀ j (hj : j < block.length), 0 < j → (block[j]).b = some (r + j - 1) := by
  have hv := valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  cases sources with
  | nil => contradiction
  | cons s ss =>
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
      intro x hx hx'
      apply (nativeTop_core_mem row r (s :: ss) x).mpr
      by_cases he : x = r
      · subst x; exact Or.inl (List.mem_of_getLast? hv.2.2.1)
      · exact Or.inr (Or.inr ⟨by omega, hx'⟩)
    by_cases hmedium : row.core.length = 2 * row.step
    · apply nativeBlockDown_medium_target_b ss.length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) ht
      simpa [nativeBlock, hmedium] using hb
    · have hbool : (row.core.length == 2 * row.step) = false :=
        Bool.eq_false_iff.mpr (by simpa using hmedium)
      have hshort : row.core.length + 1 = 2 * row.step := by
        have hs := hv.2.2.2
        unfold Row.OrdinaryShape at hs
        rcases hs with ⟨hp, hs | hs | hs⟩ <;> omega
      have hsmin : 3 ≤ row.step := by
        have hs := hv.2.2.2
        unfold Row.OrdinaryShape at hs
        rcases hs with ⟨hp, hs | hs | hs⟩ <;> omega
      apply nativeBlockDown_short_target_b (s :: ss).length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      simpa [nativeBlock, hbool] using hb

end FullMarkedBLP

