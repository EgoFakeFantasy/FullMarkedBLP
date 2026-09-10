import FullMarkedBLP.NativeHighEntryRetention
import FullMarkedBLP.NativeLowerMinimum

namespace FullMarkedBLP

theorem nativeBlockDown_short_bottom_geometry (k : Nat) {base : Nat} {top : Row} {block : Pattern}
    (valid : top.CoreValid (base + k))
    (shape : top.core.length + 1 = 2 * top.step) (steps : k + 3 ≤ top.step)
    (targets : ∀ y, base ≤ y → y ≤ base + k → y ∈ top.core)
    (run : nativeBlockDown k (base + k) false top = some block) :
    ∃ bottom, block[0]? = some bottom ∧ bottom.CoreValid base ∧
      bottom.step + k = top.step ∧ bottom.core.length + 2 * k = top.core.length ∧
      bottom.core.head? = top.core.head? := by
  induction k generalizing top block with
  | zero =>
    cases Option.some.inj run
    exact ⟨top, rfl, by simpa using valid, by omega, by omega, rfl⟩
  | succ k ih =>
    obtain ⟨lower, lowerStep, run⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨earlier, earlierRun, out⟩ := Option.bind_eq_some_iff.mp run
    change some (earlier ++ [top]) = some block at out
    cases Option.some.inj out
    have prev : base + (k + 1) - 1 = base + k := by omega
    have target := targets (base + (k + 1) - 1) (by omega) (by omega)
    have lowerValid := nativeLower_short_coreValid valid target (by omega) (by omega) shape lowerStep
    rw [prev] at lowerValid earlierRun
    have lowerShape := (nativeLower_short_shape valid (by omega) shape lowerStep).2
    have lowerSteps := nativeLower_step lowerStep
    simp only [Bool.false_eq_true, if_false] at lowerSteps
    have lowerLength := nativeLower_length valid (by omega) lowerStep
    have lowerTargets := nativeLower_preserves_targets valid targets (by omega) lowerStep
    obtain ⟨bottom, entry, bottomValid, stepEq, lenEq, headEq⟩ := ih lowerValid lowerShape
      (by omega) (fun y hy hy' => lowerTargets y hy (by omega)) earlierRun
    have len := nativeBlockDown_length earlierRun
    refine ⟨bottom, ?_, bottomValid, by omega, by omega, headEq.trans ?_⟩
    · simpa only [List.getElem?_append_left (by omega : 0 < earlier.length)] using entry
    · cases hm : top.core.head? with
      | none =>
        have empty := List.head?_eq_none_iff.mp hm
        have := valid.2.1
        simp [empty] at this
      | some minimum => exact nativeLower_preserves_minimum valid hm lowerStep

theorem nativeBlockDown_medium_bottom_geometry (k : Nat) {base : Nat} {top : Row} {block : Pattern}
    (valid : top.CoreValid (base + (k + 1)))
    (shape : top.core.length = 2 * top.step) (steps : k + 3 ≤ top.step)
    (targets : ∀ y, base ≤ y → y ≤ base + (k + 1) → y ∈ top.core)
    (run : nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    ∃ bottom, block[0]? = some bottom ∧ bottom.CoreValid base ∧
      bottom.step + k = top.step ∧ bottom.core.length + 2 * k + 1 = top.core.length ∧
      bottom.core.head? = top.core.head? := by
  let lower : Row := ⟨top.core.erase (base + (k + 1)), top.step,
    top.marks.erase (base + (k + 1) - 1)⟩
  have step : nativeLower top (base + (k + 1)) true = some lower := rfl
  obtain ⟨earlier, earlierRun, out⟩ := Option.bind_eq_some_iff.mp run
  change some (earlier ++ [top]) = some block at out
  cases Option.some.inj out
  have ownerMem := List.mem_of_getLast? valid.2.2.1
  have lowerShape := nativeLower_medium_shape ownerMem (by omega) shape step
  have prev : base + (k + 1) - 1 = base + k := by omega
  have target := targets (base + (k + 1) - 1) (by omega) (by omega)
  have lowerLen : lower.core.length = top.core.length - 1 := List.length_erase_of_mem ownerMem
  have lowerValid : lower.CoreValid (base + k) := by
    refine ⟨nativeLower_sorted valid.1 step, by have := valid.2.1; omega, ?_, lowerShape.1⟩
    simpa only [prev] using erase_owner_last valid target (by omega)
  have lowerTargets : ∀ y, base ≤ y → y ≤ base + k → y ∈ lower.core := by
    intro y hy hy'
    exact (List.mem_erase_of_ne (by omega)).mpr (targets y hy (by omega))
  rw [prev] at earlierRun
  obtain ⟨bottom, entry, bottomValid, stepEq, lenEq, headEq⟩ :=
    nativeBlockDown_short_bottom_geometry k lowerValid lowerShape.2 steps lowerTargets earlierRun
  have len := nativeBlockDown_length earlierRun
  have lowerSteps : lower.step = top.step := rfl
  refine ⟨bottom, ?_, bottomValid, by omega, by omega, headEq.trans ?_⟩
  · simpa only [List.getElem?_append_left (by omega : 0 < earlier.length)] using entry
  · cases hm : top.core.head? with
    | none =>
      have empty := List.head?_eq_none_iff.mp hm
      have := valid.2.1
      simp [empty] at this
    | some minimum => exact nativeLower_preserves_minimum valid hm step

theorem nativeBlock_bottom_geometry {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (source : nativeSources a r = some sources)
    (nonempty : sources ≠ []) (run : nativeBlock row r sources = some block) :
    ∃ bottom, block[0]? = some bottom ∧ bottom.CoreValid r ∧
      bottom.step = row.step + (if row.core.length = 2 * row.step then 1 else 0) ∧
      bottom.core.length = row.core.length + (if row.core.length = 2 * row.step then 1 else 0) ∧
      bottom.core.head? = row.core.head? := by
  have hv := valid r row hr
  have eligible := nativeSources_nonempty_eligible hr source nonempty
  have step : 2 ≤ row.step := by
    by_cases one : row.step = 1
    · exact False.elim (nonempty (Option.some.inj
        (source.symm.trans (nativeSources_step_one_empty hv hr one))))
    · have := hv.2.2.2.1; omega
  have topValid := nativeTop_actual_coreValid valid hr source
  have topLen := nativeTop_actual_length valid hr source
  have topStep : (nativeTop row r sources).step = row.step + sources.length := rfl
  have targets : ∀ y, r ≤ y → y ≤ r + sources.length → y ∈ (nativeTop row r sources).core := by
    intro y hy hy'
    apply (nativeTop_core_mem row r sources y).mpr
    by_cases eq : y = r
    · subst y; exact Or.inl (List.mem_of_getLast? hv.2.2.1)
    · exact Or.inr (Or.inr ⟨by omega, hy'⟩)
  have headEq : (nativeTop row r sources).core.head? = row.core.head? := by
    cases hm : row.core.head? with
    | none =>
      have empty := List.head?_eq_none_iff.mp hm
      have := hv.2.1
      simp [empty] at this
    | some minimum => exact nativeTop_preserves_minimum valid hr source hm
  by_cases medium : row.core.length = 2 * row.step
  · cases sources with
    | nil => contradiction
    | cons s ss =>
      have down : nativeBlockDown (ss.length + 1) (r + (ss.length + 1)) true
          (nativeTop row r (s :: ss)) = some block := by
        simpa [nativeBlock, medium] using run
      obtain ⟨bottom, entry, bottomValid, stepEq, lenEq, minimumEq⟩ :=
        nativeBlockDown_medium_bottom_geometry ss.length topValid
          (by rw [topStep]; omega) (by rw [topStep]; simp; omega) targets down
      refine ⟨bottom, entry, bottomValid, ?_, ?_, minimumEq.trans headEq⟩
      · simp only [if_pos medium]; simp only [List.length_cons] at topStep; omega
      · simp only [if_pos medium]; simp only [List.length_cons] at topLen; omega
  · have short : row.core.length + 1 = 2 * row.step := by
      have shape := hv.2.2.2
      rcases shape with ⟨_, h | h | h⟩ <;> omega
    have minStep : 3 ≤ row.step := by
      have shape := hv.2.2.2
      rcases shape with ⟨_, h | h | h⟩ <;> omega
    have down : nativeBlockDown sources.length (r + sources.length) false
        (nativeTop row r sources) = some block := by
      have hbool : (row.core.length == 2 * row.step) = false := by simp [medium]
      simpa [nativeBlock, nonempty, hbool] using run
    obtain ⟨bottom, entry, bottomValid, stepEq, lenEq, minimumEq⟩ :=
      nativeBlockDown_short_bottom_geometry sources.length topValid
        (by rw [topStep]; omega) (by rw [topStep]; omega) targets down
    refine ⟨bottom, entry, bottomValid, ?_, ?_, minimumEq.trans headEq⟩
    · simp only [if_neg medium]; omega
    · simp only [if_neg medium]; omega

end FullMarkedBLP
