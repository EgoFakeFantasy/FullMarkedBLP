import FullMarkedBLP.NativeBlockEndpoint
import FullMarkedBLP.NativeLowerTrace

namespace FullMarkedBLP

/-- A short descent retains every high core entry below the owner, whether
or not it happens to be marked. -/
theorem nativeLower_short_high_entry {row lower : Row} {owner i x : Nat}
    (valid : row.CoreValid owner) (shape : row.core.length + 1 = 2 * row.step)
    (high : row.step ≤ i) (entry : row.core[i]? = some x) (below : x < owner)
    (step : nativeLower row owner false = some lower) :
    lower.core[i - 1]? = some x := by
  obtain ⟨source, he, out⟩ := Option.bind_eq_some_iff.mp step
  have room := Row.step_lt_length valid.2.2.2
  have sourceAt : row.core[row.core.length - row.step]? = some source := by
    simpa [Row.e, fromRight, valid.2.2.2.1, Nat.le_of_lt room] using he
  obtain ⟨hs, sourceEq⟩ := List.getElem?_eq_some_iff.mp sourceAt
  obtain ⟨hi, entryEq⟩ := List.getElem?_eq_some_iff.mp entry
  have lt : source < x := by
    have ordered := List.pairwise_iff_getElem.mp valid.1 _ _ hs hi (by omega)
    simpa only [sourceEq, entryEq] using ordered
  have sourceMem : source ∈ row.core.erase owner :=
    (List.mem_erase_of_ne (by omega)).mpr (List.mem_of_getElem? sourceAt)
  have kept := erase_greater_preserves_index valid.1 entry below
  have shifted := erase_smaller_preserves_index (valid.1.sublist List.erase_sublist) kept sourceMem lt
  cases Option.some.inj out
  exact shifted

/-- During all short descents an original high entry survives to the bottom.
The statement records its exact position, not merely membership. -/
theorem nativeBlockDown_short_bottom_high_entry (k : Nat) {base i x : Nat} {top : Row} {block : Pattern}
    (valid : top.CoreValid (base + k))
    (shape : top.core.length + 1 = 2 * top.step) (steps : k + 3 ≤ top.step)
    (targets : ∀ y, base ≤ y → y ≤ base + k → y ∈ top.core)
    (high : top.step ≤ i + k) (entry : top.core[i + k]? = some x) (below : x < base)
    (run : nativeBlockDown k (base + k) false top = some block) :
    (block[0]?).bind (fun row => row.core[i]?) = some x := by
  induction k generalizing top block with
  | zero =>
    cases Option.some.inj run
    simpa using entry
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
    simp only [Bool.false_eq_true, ↓reduceIte] at lowerSteps
    have lowerTargets := nativeLower_preserves_targets valid targets (by omega) lowerStep
    have lowerEntry := nativeLower_short_high_entry valid shape high entry (by omega) lowerStep
    have shifted : lower.core[i + k]? = some x := by
      simpa only [show i + (k + 1) - 1 = i + k by omega] using lowerEntry
    have result := ih lowerValid lowerShape (by omega)
      (fun y hy hy' => lowerTargets y hy (by omega)) (by omega) shifted earlierRun
    have len := nativeBlockDown_length earlierRun
    simpa only [List.getElem?_append_left (by omega : 0 < earlier.length)] using result

/-- The initial medium exception retains the high entry without an index
shift; subsequent short descents shift it once each. -/
theorem nativeBlockDown_medium_bottom_high_entry (k : Nat) {base i x : Nat} {top : Row} {block : Pattern}
    (valid : top.CoreValid (base + (k + 1)))
    (shape : top.core.length = 2 * top.step) (steps : k + 3 ≤ top.step)
    (targets : ∀ y, base ≤ y → y ≤ base + (k + 1) → y ∈ top.core)
    (high : top.step ≤ i + k) (entry : top.core[i + k]? = some x) (below : x < base)
    (run : nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    (block[0]?).bind (fun row => row.core[i]?) = some x := by
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
  have lowerEntry : lower.core[i + k]? = some x :=
    erase_greater_preserves_index valid.1 entry (by omega)
  rw [prev] at earlierRun
  have result := nativeBlockDown_short_bottom_high_entry k lowerValid lowerShape.2 steps
    lowerTargets high lowerEntry below earlierRun
  have len := nativeBlockDown_length earlierRun
  simpa only [List.getElem?_append_left (by omega : 0 < earlier.length)] using result

end FullMarkedBLP

