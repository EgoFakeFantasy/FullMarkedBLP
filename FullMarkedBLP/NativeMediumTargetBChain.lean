import FullMarkedBLP.NativeTargetBChain

namespace FullMarkedBLP

/-- The medium first descent also retains every earlier consecutive target. -/
theorem nativeBlockDown_medium_targets (k : Nat) {base : Nat} {top : Row} {block : Pattern}
    (hv : top.CoreValid (base + (k + 1))) (hlen : top.core.length = 2 * top.step)
    (hstep : k + 3 ≤ top.step)
    (htarget : ∀ x, base ≤ x → x ≤ base + (k + 1) → x ∈ top.core)
    (h : nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    ∀ j (hj : j < block.length), ∀ x, base ≤ x → x ≤ base + j → x ∈ (block[j]).core := by
  let lower : Row := ⟨top.core.erase (base + (k + 1)), top.step,
    top.marks.erase (base + (k + 1) - 1)⟩
  have hl : nativeLower top (base + (k + 1)) true = some lower := rfl
  obtain ⟨earlier, he, h⟩ := Option.bind_eq_some_iff.mp h
  change some (earlier ++ [top]) = some block at h
  cases Option.some.inj h
  have ho : base + (k + 1) ∈ top.core := List.mem_of_getLast? hv.2.2.1
  have hs := nativeLower_medium_shape ho (by omega) hlen hl
  have hprev : base + (k + 1) - 1 = base + k := by omega
  have hm := htarget (base + (k + 1) - 1) (by omega) (by omega)
  have hlen' : lower.core.length = top.core.length - 1 := List.length_erase_of_mem ho
  have hstep' : lower.step = top.step := rfl
  have hv' : lower.CoreValid (base + k) := by
    refine ⟨nativeLower_sorted hv.1 hl, by omega, ?_, hs.1⟩
    change (top.core.erase _).getLast? = some _
    simpa [hprev] using erase_owner_last hv hm (by omega)
  have ht' : ∀ x, base ≤ x → x ≤ base + k → x ∈ lower.core := by
    intro x hx hb
    exact (List.mem_erase_of_ne (by omega)).mpr (htarget x hx (by omega))
  rw [hprev] at he
  have earlierTargets := nativeBlockDown_short_targets k hv' hs.2 (by omega) ht' he
  have hlens := nativeBlockDown_length he
  intro j hj x hx hxb
  by_cases hjl : j < earlier.length
  · rw [List.getElem_append_left hjl]
    exact earlierTargets j hjl x hx hxb
  · have hjeq : j = earlier.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    exact htarget x hx (by omega)

theorem nativeBlockDown_medium_target_b (k : Nat) {base : Nat} {top : Row} {block : Pattern}
    (hv : top.CoreValid (base + (k + 1))) (hlen : top.core.length = 2 * top.step)
    (hstep : k + 3 ≤ top.step)
    (htarget : ∀ x, base ≤ x → x ≤ base + (k + 1) → x ∈ top.core)
    (h : nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    ∀ j (hj : j < block.length), 0 < j → (block[j]).b = some (base + j - 1) := by
  obtain ⟨other, ho, valid⟩ := nativeBlockDown_medium_total k hv hlen hstep htarget
  have heq := Option.some.inj (h.symm.trans ho)
  subst other
  intro j hj hp
  have hm := nativeBlockDown_medium_targets k hv hlen hstep htarget h j hj (base + j - 1)
    (by omega) (by omega)
  have hentry := penultimate_index (valid j hj) hm (by omega)
  simpa [Row.b, fromRight, (valid j hj).2.1] using hentry

end FullMarkedBLP
