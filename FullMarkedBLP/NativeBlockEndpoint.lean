import FullMarkedBLP.NativeLowerSat

namespace FullMarkedBLP

theorem nativeBlockDown_short_e (k : Nat) {base startIndex : Nat} {top : Row} {block : Pattern}
    (hv : top.CoreValid (base + k))
    (hlen : top.core.length + 1 = 2 * top.step) (hstep : k + 3 ≤ top.step)
    (hindex : top.core.length = startIndex + k + top.step + 1)
    (htarget : ∀ x, base ≤ x → x ≤ base + k → x ∈ top.core)
    (h : nativeBlockDown k (base + k) false top = some block) :
    ∀ j (hj : j < block.length), (block[j]).e = top.core[startIndex + j + 1]? := by
  induction k generalizing top block with
  | zero =>
    cases Option.some.inj h
    intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    have hi : top.core.length - top.step = startIndex + 1 := by omega
    simp [Row.e, fromRight, show 0 < top.step by omega, hi, show top.step ≤ top.core.length by omega]
  | succ k ih =>
    obtain ⟨lower, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨earlier, he, h⟩ := Option.bind_eq_some_iff.mp h
    change some (earlier ++ [top]) = some block at h
    cases Option.some.inj h
    have hprev : base + (k + 1) - 1 = base + k := by omega
    have hm : base + (k + 1) - 1 ∈ top.core := htarget _ (by omega) (by omega)
    have hv' := nativeLower_short_coreValid hv hm (by omega) (by omega) hlen hl
    rw [hprev] at hv' he
    have hs' := (nativeLower_short_shape hv (by omega) hlen hl).2
    have hlen' := nativeLower_length hv (by omega) hl
    have hstep' := nativeLower_step hl
    simp only [Bool.false_eq_true, ↓reduceIte] at hstep'
    have ht' := nativeLower_preserves_targets hv htarget (by omega) hl
    have hi' : lower.core.length = startIndex + k + lower.step + 1 := by omega
    have hh := ih hv' hs' (by omega) hi' (fun x hx hb => ht' x hx (by omega)) he
    have heLen := nativeBlockDown_length he
    intro j hj
    by_cases hjl : j < earlier.length
    · rw [List.getElem_append_left hjl, hh j hjl]
      exact nativeLower_keeps_low_index hv (by omega) hl
    · have hjeq : j = earlier.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      subst j
      have hi : top.core.length - top.step = startIndex + (k + 1) + 1 := by omega
      simp [heLen, Row.e, fromRight, show 0 < top.step by omega, hi, show top.step ≤ top.core.length by omega]

#print axioms nativeBlockDown_short_e



theorem nativeBlockDown_medium_e (k : Nat) {base startIndex : Nat} {top : Row} {block : Pattern}
    (hv : top.CoreValid (base + (k + 1)))
    (hlen : top.core.length = 2 * top.step) (hstep : k + 3 ≤ top.step)
    (hindex : top.core.length = startIndex + (k + 1) + top.step + 1)
    (htarget : ∀ x, base ≤ x → x ≤ base + (k + 1) → x ∈ top.core)
    (h : nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    ∀ j (hj : j < block.length), (block[j]).e = top.core[startIndex + j + 1]? := by
  let lower : Row := ⟨top.core.erase (base + (k + 1)), top.step,
    top.marks.erase (base + (k + 1) - 1)⟩
  have hl : nativeLower top (base + (k + 1)) true = some lower := rfl
  obtain ⟨earlier, he, h⟩ := Option.bind_eq_some_iff.mp h
  change some (earlier ++ [top]) = some block at h
  cases Option.some.inj h
  have ho : base + (k + 1) ∈ top.core := List.mem_of_getLast? hv.2.2.1
  have hs := nativeLower_medium_shape ho (by omega) hlen hl
  have hprev : base + (k + 1) - 1 = base + k := by omega
  have hm : base + (k + 1) - 1 ∈ top.core := htarget _ (by omega) (by omega)
  have hout : lower = ⟨top.core.erase (base + (k + 1)), top.step,
      top.marks.erase (base + (k + 1) - 1)⟩ := (Option.some.inj hl).symm
  have hlen' : lower.core.length = top.core.length - 1 := by
    rw [hout]; exact List.length_erase_of_mem ho
  have hstep' : lower.step = top.step := by rw [hout]
  have hv' : lower.CoreValid (base + k) := by
    refine ⟨nativeLower_sorted hv.1 hl, by omega, ?_, hs.1⟩
    rw [hout]
    simpa [hprev] using erase_owner_last hv hm (by omega)
  have ht' : ∀ x, base ≤ x → x ≤ base + k → x ∈ lower.core := by
    intro x hx hb
    rw [hout]
    exact (List.mem_erase_of_ne (by omega)).mpr (htarget x hx (by omega))
  rw [hprev] at he
  have hi' : lower.core.length = startIndex + k + lower.step + 1 := by omega
  have hh := nativeBlockDown_short_e k hv' hs.2 (by omega) hi' ht' he
  have heLen := nativeBlockDown_length he
  intro j hj
  by_cases hjl : j < earlier.length
  · rw [List.getElem_append_left hjl, hh j hjl]
    exact nativeLower_keeps_low_index hv (by omega) hl
  · have hjeq : j = earlier.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    have hi : top.core.length - top.step = startIndex + (k + 1) + 1 := by omega
    simp [heLen, Row.e, fromRight, show 0 < top.step by omega, hi, show top.step ≤ top.core.length by omega]

#print axioms nativeBlockDown_medium_e

theorem nativeBlock_actual_e {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    (hne : sources ≠ []) (hb : nativeBlock row r sources = some block) :
    ∀ j (hj : j < block.length), (block[j]).e =
      (nativeTop row r sources).core[row.core.length - (row.step + 1) + j + 1]? := by
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
    · apply nativeBlockDown_medium_e ss.length htop
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
      apply nativeBlockDown_short_e (s :: ss).length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) hindex ht
      simpa [nativeBlock, hbool] using hb

/-- Adjacent block rows link the lower e to the upper p. -/
theorem nativeBlock_adjacent_ep {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r j : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    (hne : sources ≠ []) (hb : nativeBlock row r sources = some block)
    (hj : j + 1 < block.length) :
    (block[j]'(by omega)).e = (block[j + 1]).p := by
  rw [nativeBlock_actual_e valid hr h hne hb j (by omega),
    nativeBlock_actual_p valid hr h hne hb (j + 1) hj]
  simp only [Nat.add_assoc]

theorem nativeBlock_source_e {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e x : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (h : nativeSources a r = some sources) (hx : x ∈ sources)
    (hb : nativeBlock row r sources = some block) :
    (block[(sources.filter (· < x)).length]?).bind Row.e = some x := by
  have hne : sources ≠ [] := by intro heq; simp [heq] at hx
  have hlt : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have hlen := nativeBlock_length hb
  have hi : (sources.filter (· < x)).length + 1 < block.length := by omega
  have hsource := nativeBlock_source_p valid hr hp he h hx hb
  have hadj := nativeBlock_adjacent_ep valid hr h hne hb hi
  simpa only [List.getElem?_eq_getElem (by omega : (sources.filter (· < x)).length < block.length),
    List.getElem?_eq_getElem hi, Option.bind_some, ← hadj] using hsource

end FullMarkedBLP


