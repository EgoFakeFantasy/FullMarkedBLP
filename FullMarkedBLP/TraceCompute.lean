import FullMarkedBLP.Root

namespace FullMarkedBLP

theorem fromRight_lt_last {xs : List Nat} {r k v : Nat}
    (hs : xs.Pairwise (· < ·)) (hl : xs.getLast? = some r)
    (hk : 1 < k) (hv : fromRight xs k = some v) : v < r := by
  unfold fromRight at hv
  split at hv
  next h =>
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hv
    rw [List.getLast?_eq_getElem?] at hl
    obtain ⟨hj, hf⟩ := List.getElem?_eq_some_iff.mp hl
    have hh := List.pairwise_iff_getElem.mp hs (xs.length - k)
      (xs.length - 1) hi hj (by omega)
    simpa [he, hf] using hh
  next => simp at hv

theorem predecessor_lt {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p : Nat} (hp : predecessor a r = some p) : p < r := by
  unfold predecessor at hp
  cases hr : rowAt a r with
  | none => simp [hr] at hp
  | some row =>
    simp [hr] at hp
    have hv := valid r row hr
    exact fromRight_lt_last hv.1 hv.2.2.1 (by have := hv.2.2.2.1; omega) hp

/-- Trace computation has an explicit recursion budget. Completeness below
will supply a budget from the decreasing row indices, never a search cap. -/
def traceFuel (a : Pattern) (source : Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, y =>
    if y = source then some [y]
    else if source < y then do
      let z ← predecessor a y
      let tail ← traceFuel a source fuel z
      pure (y :: tail)
    else none

theorem traceFuel_sound {a : Pattern} {s fuel y : Nat} {xs : List Nat}
    (h : traceFuel a s fuel y = some xs) : Trace a s y xs := by
  induction fuel generalizing y xs with
  | zero => simp [traceFuel] at h
  | succ fuel ih =>
    simp only [traceFuel] at h
    split at h
    next he =>
      subst y
      simp at h
      subst xs
      exact Trace.stop
    next he =>
      split at h
      next hlt =>
        cases hp : predecessor a y with
        | none => simp [hp] at h
        | some z =>
          cases ht : traceFuel a s fuel z with
          | none => simp [hp, ht] at h
          | some tail =>
            simp [hp, ht] at h
            subst xs
            exact Trace.next hlt hp (ih ht)
      next => simp at h

/-- Every actual trace is computed once its finite length fits the budget. -/
theorem traceFuel_complete {a : Pattern} {s y : Nat} {xs : List Nat}
    (h : Trace a s y xs) : ∀ fuel, xs.length ≤ fuel →
    traceFuel a s fuel y = some xs := by
  induction h with
  | stop =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel => simp [traceFuel]
  | next hlt hp ht ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hh := ih fuel (by simpa using hf)
      simp [traceFuel, Nat.ne_of_gt hlt, hlt, hp, hh]

#print axioms predecessor_lt
#print axioms traceFuel_sound
#print axioms traceFuel_complete



theorem trace_length_bound {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s y : Nat} {xs : List Nat} (h : Trace a s y xs) : xs.length ≤ y + 1 := by
  induction h with
  | stop => simp
  | next _ hp _ ih =>
    have hd := predecessor_lt valid hp
    simp only [List.length_cons]
    omega

/-- The budget is a proved bound from the starting row, not a parameter cap. -/
def computeTrace (a : Pattern) (source y : Nat) : Option (List Nat) :=
  traceFuel a source (y + 1) y

theorem computeTrace_iff {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s y : Nat} {xs : List Nat} :
    computeTrace a s y = some xs ↔ Trace a s y xs := by
  constructor
  · exact traceFuel_sound
  · intro h
    exact traceFuel_complete h _ (trace_length_bound valid h)

/-- Compute the actual word at a marked or unmarked step-target position. -/
def computeMarkTrace (a : Pattern) (owner y : Nat) : Option (List Nat) := do
  let row ← rowAt a owner
  let k ← row.core.findIdx? (· == y)
  if k < row.step then none else do
    let source ← row.core[k - row.step]?
    computeTrace a source y

#print axioms computeTrace_iff
end FullMarkedBLP
