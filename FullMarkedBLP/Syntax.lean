import Std

/-! Literal cores omit the implicit right endpoint. Mark legality and the
generation operations are separate obligations, not assumed by this module. -/
namespace FullMarkedBLP

structure Row where
  core : List Nat
  step : Nat
  marks : List Nat
  deriving DecidableEq, Repr

abbrev Pattern := List Row

def Row.full (r : Nat) (a : Row) : List Nat := a.core ++ [r + 1]

/-- The ordinary row-length alternatives, in core-length convention. -/
def Row.OrdinaryShape (a : Row) : Prop :=
  0 < a.step ∧
    (a.core.length = 2 * a.step ∨
     (a.core.length = 3 ∧ a.step = 1) ∨
     (4 < a.core.length + 1 ∧
       (a.core.length + 1 = 2 * a.step ∨
        a.core.length + 1 = 2 * (a.step + 1))))

instance (a : Row) : Decidable a.OrdinaryShape := inferInstanceAs (Decidable (_ ∧ _))

/-- Indices here are zero-based; paper row numbers are one-based. -/
def Row.CoreValid (r : Nat) (a : Row) : Prop :=
  a.core.Pairwise (· < ·) ∧ 2 ≤ a.core.length ∧
  a.core.getLast? = some r ∧ a.OrdinaryShape

def Row.shortKey (a : Row) : List Nat :=
  (a.core.drop a.step).reverse ++ a.core.take 1

def shortKey (a : Pattern) : List (List Nat) := a.map Row.shortKey

def zero : Pattern := [⟨[0, 1], 1, []⟩, ⟨[0, 1, 2], 1, []⟩]

def start : Pattern := zero ++
  [⟨[0, 1, 2, 3], 2, []⟩,
   ⟨[0, 1, 2, 3, 4], 2, [3]⟩,
   ⟨[2, 3, 4, 5], 2, []⟩]

/-- Cut is unavailable at or below the two-row zero term. -/
def cut (a : Pattern) : Option Pattern :=
  if 2 < a.length then some a.dropLast else none

theorem zero_cut : cut zero = none := by decide

theorem start_key : shortKey start =
    [[1, 0], [2, 1, 0], [3, 2, 0], [4, 3, 2, 0], [5, 4, 2]] := by decide

theorem start_shapes : ∀ a ∈ start, a.OrdinaryShape := by
  intro a ha
  simp [start, zero] at ha
  rcases ha with h | h | h | h | h <;> subst a <;> decide

theorem shortKey_append (a b : Pattern) :
    shortKey (a ++ b) = shortKey a ++ shortKey b := by
  simp [shortKey]

theorem row_key_ignores_marks (a : Row) (marks : List Nat) :
    ({a with marks := marks} : Row).shortKey = a.shortKey := rfl

end FullMarkedBLP
