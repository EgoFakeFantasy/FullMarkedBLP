import FullMarkedBLP.FrozenMarks

namespace FullMarkedBLP

theorem currentPlusOne_long_cons (a : Pattern) (parent child next : Nat) (tail : List Nat) :
    currentPlusOne a (parent :: child :: next :: tail) =
      ((rowAt a parent).any (fun row => row.core.contains (child + 1)) &&
        currentPlusOne a (child :: next :: tail)) := by
  simp [currentPlusOne]

theorem currentPlusOne_tail {a : Pattern} {parent : Nat} {tail : List Nat}
    (h : currentPlusOne a (parent :: tail) = true) : currentPlusOne a tail = true := by
  cases tail with
  | nil => rfl
  | cons child tail =>
    cases tail with
    | nil => rfl
    | cons next tail =>
      rw [currentPlusOne_long_cons] at h
      exact (Bool.and_eq_true_iff.mp h).2

theorem trace_source_le_head {a : Pattern} {s y : Nat} {xs : List Nat}
    (h : Trace a s y xs) : s ≤ y := by
  cases h with
  | stop => exact Nat.le_refl _
  | next hlt _ _ => exact Nat.le_of_lt hlt

/-- Actual predecessor equations and the last endpoint determine a trace. -/
theorem trace_of_chain {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {y s : Nat} {tail : List Nat}
    (hlast : (y :: tail).getLast? = some s)
    (hedges : ∀ u v, (u, v) ∈ (y :: tail).zip tail → predecessor a u = some v) :
    Trace a s y (y :: tail) := by
  induction tail generalizing y with
  | nil =>
    have he : y = s := by simpa using hlast
    subst y
    exact Trace.stop
  | cons z tail ih =>
    have hp := hedges y z (by simp)
    have hlast' : (z :: tail).getLast? = some s := by simpa using hlast
    have ht := ih hlast' (fun u v hmem => hedges u v (by simp [hmem]))
    have hz := predecessor_lt valid hp
    have hs := trace_source_le_head ht
    exact Trace.next (by omega) hp ht

end FullMarkedBLP

