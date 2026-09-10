import FullMarkedBLP.RowTraces

namespace FullMarkedBLP

def BlockTraces (a : Pattern) (block : Pattern) : Prop :=
  ∀ i (hi : i < block.length), (block[i]).HasTraces a

theorem nativeBlockDown_short_traces (k : Nat) {a : Pattern} {base : Nat} {top : Row}
    (hv : top.CoreValid (base + k)) (hmarks : top.ProperMarks (base + k))
    (htraces : top.HasTraces a)
    (hlen : top.core.length + 1 = 2 * top.step) (hstep : k + 3 ≤ top.step)
    (htarget : ∀ x, base ≤ x → x ≤ base + k → x ∈ top.core) :
    ∃ block, nativeBlockDown k (base + k) false top = some block ∧ BlockTraces a block := by
  induction k generalizing top with
  | zero =>
    refine ⟨[top], rfl, ?_⟩
    intro i hi
    have : i = 0 := by simpa using hi
    subst i
    simpa using htraces
  | succ k ih =>
    obtain ⟨lower, hl⟩ := nativeLower_exists (owner := base + (k + 1)) false hv.2.2.2
    have hprev : base + (k + 1) - 1 = base + k := by omega
    have hm : base + (k + 1) - 1 ∈ top.core := htarget _ (by omega) (by omega)
    have hvalid := nativeLower_short_coreValid hv hm (by omega) (by omega) hlen hl
    have hproper := nativeLower_short_proper hv hmarks hlen hl
    have htraceLower := nativeLower_short_traces hv hmarks hlen htraces hl
    rw [hprev] at hvalid hproper
    have hshape := (nativeLower_short_shape hv (by omega) hlen hl).2
    have hs := nativeLower_step hl
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have ht := nativeLower_preserves_targets hv htarget (by omega) hl
    obtain ⟨earlier, he, hev⟩ := ih hvalid hproper htraceLower hshape (by omega)
      (fun x hx hb => ht x hx (by omega))
    have heLen := nativeBlockDown_length he
    refine ⟨earlier ++ [top], ?_, ?_⟩
    · simp [nativeBlockDown, hl, hprev, he]
    · intro i hi
      by_cases hb : i < earlier.length
      · simpa only [List.getElem_append_left hb] using hev i hb
      · have hieq : i = earlier.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        subst i
        simpa [heLen, Nat.add_assoc] using htraces

theorem nativeBlockDown_medium_traces (k : Nat) {a : Pattern} {base : Nat} {top : Row}
    (hv : top.CoreValid (base + (k + 1))) (hmarks : top.ProperMarks (base + (k + 1)))
    (htraces : top.HasTraces a)
    (hlen : top.core.length = 2 * top.step) (hstep : k + 3 ≤ top.step)
    (htarget : ∀ x, base ≤ x → x ≤ base + (k + 1) → x ∈ top.core) :
    ∃ block, nativeBlockDown (k + 1) (base + (k + 1)) true top = some block ∧
      BlockTraces a block := by
  let lower : Row := ⟨top.core.erase (base + (k + 1)), top.step,
    top.marks.erase (base + (k + 1) - 1)⟩
  have hl : nativeLower top (base + (k + 1)) true = some lower := rfl
  have ho : base + (k + 1) ∈ top.core := List.mem_of_getLast? hv.2.2.1
  have hshape := nativeLower_medium_shape ho (by omega) hlen hl
  have hm : base + (k + 1) - 1 ∈ top.core := htarget _ (by omega) (by omega)
  have hprev : base + (k + 1) - 1 = base + k := by omega
  have hvalid : lower.CoreValid (base + k) := by
    simpa only [hprev] using nativeLower_medium_coreValid hv hm (by omega) (by omega) hlen hl
  have hproper : lower.ProperMarks (base + k) := by
    simpa [hprev] using nativeLower_medium_proper hv hmarks hl
  have ht : ∀ x, base ≤ x → x ≤ base + k → x ∈ lower.core := by
    intro x hx hb
    exact (List.mem_erase_of_ne (by omega)).mpr (htarget x hx (by omega))
  obtain ⟨earlier, he, hev⟩ := nativeBlockDown_short_traces k hvalid hproper (nativeLower_medium_traces hv hmarks htraces hl) hshape.2 hstep ht
  have heLen := nativeBlockDown_length he
  refine ⟨earlier ++ [top], ?_, ?_⟩
  · simp [nativeBlockDown, hl, hprev, he]
  · intro i hi
    by_cases hb : i < earlier.length
    · simpa only [List.getElem_append_left hb] using hev i hb
    · have hieq : i = earlier.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      subst i
      simpa [heLen, Nat.add_assoc] using htraces

end FullMarkedBLP
