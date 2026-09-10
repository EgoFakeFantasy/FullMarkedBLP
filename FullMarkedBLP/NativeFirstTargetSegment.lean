import FullMarkedBLP.NativeTargetEntry

namespace FullMarkedBLP

/-- An arbitrary starting endpoint whose B is the segment top yields exactly that segment size. -/
theorem nativeSourcesFuel_exact_length_of_first_target {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {fuel u base top : Nat} {sources : List Nat}
    (walk : nativeSourcesFuel a base fuel u = some sources)
    (first : (rowAt a u).bind Row.b = some (base + top)) (positive : 0 < top)
    (chain : ∀ j, 0 < j → j ≤ top →
      (rowAt a (base + j)).bind Row.b = some (base + j - 1)) :
    sources.length = top ∧ ∀ j, 0 < j → j ≤ top → base + j ∈ sources := by
  have entered := nativeSourcesFuel_first_mem walk first (by omega)
  have members := nativeSourcesFuel_contains_target_segment walk (Nat.le_refl _) entered chain
  have lower := nativeSourcesFuel_target_segment_length walk (Nat.le_refl _) entered chain
  have above := nativeSourcesFuel_above_threshold walk
  have cap : ∀ x ∈ sources, x ≤ base + top := by
    cases fuel with
    | zero => simp [nativeSourcesFuel] at walk
    | succ fuel =>
      obtain ⟨row, atRow, rest⟩ := Option.bind_eq_some_iff.mp walk
      obtain ⟨next, atNext, rest⟩ := Option.bind_eq_some_iff.mp rest
      have eq : next = base + top := by
        simpa only [atRow, Option.bind_some, atNext, Option.some.injEq] using first
      split at rest
      next gt =>
        obtain ⟨tail, tailWalk, same⟩ := Option.bind_eq_some_iff.mp rest
        cases Option.some.inj same
        intro x mem
        rcases List.mem_cons.mp mem with same | mem
        · omega
        · have bounds := nativeSourcesFuel_bounds valid tailWalk x mem
          omega
      next no => omega
  let targets := (List.range top).map (fun j => base + 1 + j)
  have upper : sources.length ≤ top := by
    have bound := nodup_subset_length (nativeSourcesFuel_nodup_of_success walk) (ys := targets) (by
      intro x mem
      have lo := above x mem
      have hi := cap x mem
      apply List.mem_map.mpr
      exact ⟨x - base - 1, List.mem_range.mpr (by omega), by omega⟩)
    simpa only [targets, List.length_map, List.length_range] using bound
  exact ⟨by omega, members⟩

end FullMarkedBLP
