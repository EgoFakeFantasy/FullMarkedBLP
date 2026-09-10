import FullMarkedBLP.NativeRank

namespace FullMarkedBLP

theorem nativeBlock_actual_p {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    (hne : sources ≠ []) (hb : nativeBlock row r sources = some block) :
    ∀ j (hj : j < block.length), (block[j]).p =
      (nativeTop row r sources).core[row.core.length - (row.step + 1) + j]? := by
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
    have hindex : (nativeTop row r (s :: ss)).core.length =
        row.core.length - (row.step + 1) + (s :: ss).length +
          (nativeTop row r (s :: ss)).step + 1 := by
      change _ = _ + _ + (row.step + (s :: ss).length) + 1
      omega
    have ht : ∀ x, r ≤ x → x ≤ r + (s :: ss).length →
        x ∈ (nativeTop row r (s :: ss)).core := by
      intro x hx hx'
      apply (nativeTop_core_mem row r (s :: ss) x).mpr
      by_cases he : x = r
      · subst x; exact Or.inl (List.mem_of_getLast? hv.2.2.1)
      · exact Or.inr (Or.inr ⟨by omega, hx'⟩)
    by_cases hmedium : row.core.length = 2 * row.step
    · apply nativeBlockDown_medium_p ss.length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) hindex ht
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
      apply nativeBlockDown_short_p (s :: ss).length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) hindex ht
      simpa [nativeBlock, hbool] using hb

theorem nativeBlock_bottom_p {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (hp : row.p = some p)
    (h : nativeSources a r = some sources) (hb : nativeBlock row r sources = some block) :
    (block.head?).bind Row.p = some p := by
  by_cases hn : sources = []
  · subst sources
    have he : block = [row] := by simpa [nativeBlock] using hb.symm
    simpa [he] using hp
  · have hl := nativeBlock_length hb
    have hi : 0 < block.length := by omega
    have hh := nativeBlock_actual_p valid hr h hn hb 0 hi
    have he := nativeTop_old_p_entry valid hr hp h
    have hhead : block.head? = some block[0] := by simp [List.head?_eq_getElem?, hi]
    simpa [hhead, he] using hh

#print axioms nativeBlock_bottom_p
end FullMarkedBLP
