import FullMarkedBLP.Root

namespace FullMarkedBLP

/-- The short-copy map in core convention. The source endpoint is checked,
including when this is used on the implicit endpoint of a source row.
No semantic criterion is used to decide whether the map is defined. -/
def copyEntry (n : Nat) (last : Row) (x : Nat) : Option Nat := do
  let a ← last.core.head?
  let p ← last.p
  let e ← last.e
  if p = 0 then none
  else if e < x then none
  else if x < a then some x
  else if p ≤ x then some (x + (n - p))
  else
    let pair ← (last.core.zip (last.core.drop last.step)).find? (fun pair => pair.1 == x)
    some pair.2

/-- Copy the entire ordinary row first, then omit its implicit endpoint.
Marks are deliberately not part of this intermediate result. -/
def copiedCore (n : Nat) (last : Row) (source : Nat) (row : Row) : Option (List Nat) := do
  let full ← (row.full source).mapM (copyEntry n last)
  pure full.dropLast

/-- Short-copy source indices are p,...,e-1; p=0 is undefined. -/
def shortCopySources (last : Row) : Option (List Nat) := do
  let p ← last.p
  let e ← last.e
  if p = 0 then none else some ((List.range (e - p)).map (p + ·))

/-- All required source rows and all their full entries must exist. This is
only the unmarked skeleton, not the marked short-copy operation. -/
def shortCopySkeleton (a : Pattern) : Option (List (List Nat × Nat)) := do
  let last ← a.getLast?
  let sources ← shortCopySources last
  sources.mapM fun source => do
    let row ← rowAt a source
    let core ← copiedCore a.length last source row
    pure (core, row.step)

theorem copyEntry_zero_source (n : Nat) (last : Row) (x : Nat)
    (hp : last.p = some 0) : copyEntry n last x = none := by
  simp [copyEntry, hp]


theorem start_copy_skeleton : shortCopySkeleton start =
    some [([0, 1, 4, 5], 2)] := by decide

/-- The same threshold case used by the auxiliary E recursion. -/
theorem auxiliary_copy_entry (a n x : Nat) (ha : 0 < a)
    (hx : x ≤ n) :
    copyEntry n ⟨[a, n], 1, []⟩ x =
      some (if x < a then x else x + (n - a)) := by
  have hne : a ≠ 0 := by omega
  simp [copyEntry, Row.p, Row.e, fromRight, hne, Nat.not_lt.mpr hx]
  split
  · rfl
  · rename_i h
    simp [Nat.le_of_not_gt h]

end FullMarkedBLP
