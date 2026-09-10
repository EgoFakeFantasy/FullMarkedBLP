import FullMarkedBLP.NativeHighEntryRetention
import FullMarkedBLP.NativeBottomBound

namespace FullMarkedBLP

/-- The original B survives in the bottom core of every nonempty native block. -/
theorem nativeBlock_bottom_contains_b {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r v : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (source : nativeSources a r = some sources)
    (nonempty : sources ≠ []) (hb : row.b = some v)
    (run : nativeBlock row r sources = some block) :
    ∃ bottom, block[0]? = some bottom ∧ v ∈ bottom.core := by
  have hv := valid r row hr
  have room := Row.step_lt_length hv.2.2.2
  have eligible := nativeSources_nonempty_eligible hr source nonempty
  have step : 2 ≤ row.step := by
    by_cases one : row.step = 1
    · have empty := nativeSources_step_one_empty hv hr one
      exact False.elim (nonempty (Option.some.inj (source.symm.trans empty)))
    · have := hv.2.2.2.1; omega
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) (by omega) (by omega)
  have elt := fromRight_lt_last hv.1 hv.2.2.1 (by omega : 1 < row.step) he
  have emem : e ∈ row.core := by
    unfold fromRight at he
    split at he
    next => exact List.mem_of_getElem? he
    next => simp at he
  have eb := core_entry_le_b hv hb emem elt
  have vlt := fromRight_lt_last hv.1 hv.2.2.1 (by decide : 1 < 2) hb
  have vi : row.core[row.core.length - 2]? = some v := by
    simpa [Row.b, fromRight, show 2 ≤ row.core.length from hv.2.1] using hb
  have filter : sources.filter (· < v) = sources := by
    apply List.filter_eq_self.mpr
    intro x hx
    have bound := nativeSources_between valid hr hp he source x hx
    simp only [decide_eq_true_eq]; omega
  have rank := nativeTop_rank_exact valid hr source (Nat.le_of_lt vlt)
  rw [filter, sorted_rank_at_index hv.1 vi] at rank
  have mem := (nativeTop_core_mem row r sources v).mpr (Or.inl (List.mem_of_getElem? vi))
  have topEntry : (nativeTop row r sources).core[row.core.length - 2 + sources.length]? = some v := by
    simpa only [rank] using sorted_get_at_rank (nativeTop_sorted row r sources).1 mem
  have topValid := nativeTop_actual_coreValid valid hr source
  have topLen := nativeTop_actual_length valid hr source
  have targets : ∀ x, r ≤ x → x ≤ r + sources.length → x ∈ (nativeTop row r sources).core := by
    intro x hx hx'
    apply (nativeTop_core_mem row r sources x).mpr
    by_cases eq : x = r
    · subst x; exact Or.inl (List.mem_of_getLast? hv.2.2.1)
    · exact Or.inr (Or.inr ⟨by omega, hx'⟩)
  have retained : ∃ i : Nat, (block[0]?).bind (fun bottom => bottom.core[i]?) = some v := by
    by_cases medium : row.core.length = 2 * row.step
    · cases sources with
      | nil => contradiction
      | cons s ss =>
        refine ⟨row.core.length - 1, ?_⟩
        apply nativeBlockDown_medium_bottom_high_entry ss.length topValid
          (by change _ = 2 * (row.step + (s :: ss).length); omega)
          (by change _ ≤ row.step + (s :: ss).length; simp; omega) targets
          (by change row.step + (s :: ss).length ≤ _; simp; omega)
          (by simpa only [show row.core.length - 2 + (s :: ss).length = row.core.length - 1 + ss.length by simp only [List.length_cons]; omega] using topEntry) vlt
        simpa [nativeBlock, medium] using run
    · have short : row.core.length + 1 = 2 * row.step := by
        have shape := hv.2.2.2
        rcases shape with ⟨_, h | h | h⟩ <;> omega
      have minStep : 3 ≤ row.step := by
        have shape := hv.2.2.2
        rcases shape with ⟨_, h | h | h⟩ <;> omega
      refine ⟨row.core.length - 2, ?_⟩
      apply nativeBlockDown_short_bottom_high_entry sources.length topValid
        (by change _ = 2 * (row.step + sources.length); omega)
        (by change _ ≤ row.step + sources.length; omega) targets
        (by change row.step + sources.length ≤ _; omega) topEntry vlt
      have hbool : (row.core.length == 2 * row.step) = false := by simp [medium]
      simpa [nativeBlock, nonempty, hbool] using run
  obtain ⟨i, kept⟩ := retained
  obtain ⟨bottom, atBottom, entry⟩ := Option.bind_eq_some_iff.mp kept
  exact ⟨bottom, atBottom, List.mem_of_getElem? entry⟩

/-- Native preserves the bottom B exactly, including empty native steps. -/
theorem native_bottom_b_eq {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r v : Nat} {row bottom : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (birth : native a r = some (b, sources))
    (atBottom : rowAt b r = some bottom) (hb : row.b = some v) : bottom.b = some v := by
  by_cases empty : sources = []
  · subst sources
    have same := native_empty hr (native_sources_of_success birth)
    have ab : b = a := (Prod.mk.inj (Option.some.inj (birth.symm.trans same))).1
    subst b
    have rows : bottom = row := Option.some.inj (atBottom.symm.trans hr)
    simpa only [rows] using hb
  · have source := native_sources_of_success birth
    have out := birth
    unfold native at out
    rw [hr] at out
    dsimp only [Bind.bind, Option.bind] at out
    rw [source] at out
    dsimp only [Bind.bind, Option.bind] at out
    obtain ⟨block, run, out⟩ := Option.bind_eq_some_iff.mp out
    have pattern := (Prod.mk.inj (Option.some.inj out)).1
    obtain ⟨actualBottom, actualAt, kept⟩ := nativeBlock_bottom_contains_b valid hr source empty hb run
    have len := nativeBlock_length run
    have lookup := native_block_rowAt (sources := sources) hr (by omega : 0 < block.length)
    have atZero : rowAt b r = block[0]? := by simpa only [pattern, Nat.add_zero] using lookup
    have rows : actualBottom = bottom := Option.some.inj (actualAt.symm.trans (atZero.symm.trans atBottom))
    subst actualBottom
    have bottomValid := native_preserves_coreValid valid birth r bottom atBottom
    obtain ⟨w, hw⟩ := Row.b_exists bottomValid
    have upper := native_bottom_b_le valid hr birth empty atBottom hb hw
    have lower := core_entry_le_b bottomValid hw kept
      (fromRight_lt_last (valid r row hr).1 (valid r row hr).2.2.1 (by decide : 1 < 2) hb)
    have eq : w = v := by omega
    simpa only [eq] using hw

end FullMarkedBLP



