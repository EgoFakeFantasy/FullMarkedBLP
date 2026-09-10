import FullMarkedBLP.NativeWalkTargetSegment

namespace FullMarkedBLP

/-- Reaching a low target forces entry at the top when no B edge jumps into the interior. -/
theorem nativeSourcesFuel_enters_segment_of_no_jump {a : Pattern}
    {base top fuel u : Nat} {sources : List Nat}
    (walk : nativeSourcesFuel a base fuel u = some sources)
    (startAbove : base + top < u) (positive : 0 < top)
    (reaches : base + 1 ∈ sources)
    (noJump : ∀ z next, base + top < z → (rowAt a z).bind Row.b = some next →
      next ≤ base ∨ base + top ≤ next) : base + top ∈ sources := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at walk
  | succ fuel ih =>
    obtain ⟨row, atRow, rest⟩ := Option.bind_eq_some_iff.mp walk
    obtain ⟨next, atNext, rest⟩ := Option.bind_eq_some_iff.mp rest
    split at rest
    next greater =>
      obtain ⟨tail, tailWalk, eq⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj eq
      have edge : (rowAt a u).bind Row.b = some next := by
        simp only [atRow, Option.bind_some]
        exact atNext
      have bound : base + top ≤ next := by
        rcases noJump u next startAbove edge with low | high
        · omega
        · exact high
      by_cases topHit : next = base + top
      · simp [topHit]
      · have tailReaches : base + 1 ∈ tail := by
          rcases List.mem_cons.mp reaches with eq | mem
          · omega
          · exact mem
        exact List.mem_cons_of_mem next (ih tailWalk (by omega) tailReaches)
    next notGreater =>
      have empty : sources = [] := by simpa using rest.symm
      simp [empty] at reaches

/-- The same no-jump condition yields every member of the consecutive target segment. -/
theorem nativeSourcesFuel_full_segment_of_no_jump {a : Pattern}
    {base top fuel u : Nat} {sources : List Nat}
    (walk : nativeSourcesFuel a base fuel u = some sources)
    (startAbove : base + top < u) (positive : 0 < top)
    (reaches : base + 1 ∈ sources)
    (noJump : ∀ z next, base + top < z → (rowAt a z).bind Row.b = some next →
      next ≤ base ∨ base + top ≤ next)
    (chain : ∀ j, 0 < j → j ≤ top → (rowAt a (base + j)).bind Row.b = some (base + j - 1)) :
    ∀ j, 0 < j → j ≤ top → base + j ∈ sources := by
  exact nativeSourcesFuel_contains_target_segment walk (Nat.le_refl _)
    (nativeSourcesFuel_enters_segment_of_no_jump walk startAbove positive reaches noJump) chain

end FullMarkedBLP
