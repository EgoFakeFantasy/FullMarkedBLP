import FullMarkedBLP.NativeBlockEndpoint

namespace FullMarkedBLP

/-- Every short-descent row retains its full initial segment of native targets. -/
theorem nativeBlockDown_short_targets (k : Nat) {base : Nat} {top : Row} {block : Pattern}
    (hv : top.CoreValid (base + k)) (hlen : top.core.length + 1 = 2 * top.step)
    (hstep : k + 3 ≤ top.step)
    (htarget : ∀ x, base ≤ x → x ≤ base + k → x ∈ top.core)
    (h : nativeBlockDown k (base + k) false top = some block) :
    ∀ j (hj : j < block.length), ∀ x, base ≤ x → x ≤ base + j → x ∈ (block[j]).core := by
  induction k generalizing top block with
  | zero =>
    cases Option.some.inj h
    intro j hj x hx hxb
    have hj0 : j = 0 := by simpa using hj
    subst j
    exact htarget x hx hxb
  | succ k ih =>
    obtain ⟨lower, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨earlier, he, h⟩ := Option.bind_eq_some_iff.mp h
    change some (earlier ++ [top]) = some block at h
    cases Option.some.inj h
    have hprev : base + (k + 1) - 1 = base + k := by omega
    have hm := htarget (base + (k + 1) - 1) (by omega) (by omega)
    have hv' := nativeLower_short_coreValid hv hm (by omega) (by omega) hlen hl
    rw [hprev] at hv' he
    have hshape := (nativeLower_short_shape hv (by omega) hlen hl).2
    have hs := nativeLower_step hl
    simp only [Bool.false_eq_true, if_false] at hs
    have kept := nativeLower_preserves_targets hv htarget (by omega) hl
    have earlierTargets := ih hv' hshape (by omega) (fun x hx hb => kept x hx (by omega)) he
    have hlens := nativeBlockDown_length he
    intro j hj x hx hxb
    by_cases hjl : j < earlier.length
    · rw [List.getElem_append_left hjl]
      exact earlierTargets j hjl x hx hxb
    · have hjeq : j = earlier.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      subst j
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact htarget x hx (by omega)

/-- Adjacent inserted targets are linked by literal B edges in a short block. -/
theorem nativeBlockDown_short_target_b (k : Nat) {base : Nat} {top : Row} {block : Pattern}
    (hv : top.CoreValid (base + k)) (hlen : top.core.length + 1 = 2 * top.step)
    (hstep : k + 3 ≤ top.step)
    (htarget : ∀ x, base ≤ x → x ≤ base + k → x ∈ top.core)
    (h : nativeBlockDown k (base + k) false top = some block) :
    ∀ j (hj : j < block.length), 0 < j → (block[j]).b = some (base + j - 1) := by
  obtain ⟨other, ho, valid⟩ := nativeBlockDown_short_total k hv hlen hstep htarget
  have heq := Option.some.inj (h.symm.trans ho)
  subst other
  intro j hj hp
  have hm := nativeBlockDown_short_targets k hv hlen hstep htarget h j hj (base + j - 1)
    (by omega) (by omega)
  have hentry := penultimate_index (valid j hj) hm (by omega)
  simpa [Row.b, fromRight, (valid j hj).2.1] using hentry

end FullMarkedBLP
