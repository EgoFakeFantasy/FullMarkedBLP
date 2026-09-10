import FullMarkedBLP.Syntax

namespace FullMarkedBLP

/-- Access from the right is partial, including at index zero. -/
def fromRight (xs : List Nat) (k : Nat) : Option Nat :=
  if 0 < k ∧ k ≤ xs.length then xs[xs.length - k]? else none

def Row.p (a : Row) : Option Nat := fromRight a.core (a.step + 1)
def Row.e (a : Row) : Option Nat := fromRight a.core a.step
def Row.b (a : Row) : Option Nat := fromRight a.core 2

/-- Row zero does not exist. -/
def rowAt (a : Pattern) (r : Nat) : Option Row :=
  if r = 0 then none else a[r - 1]?

def predecessor (a : Pattern) (r : Nat) : Option Nat :=
  (rowAt a r).bind Row.p

/-- Finite actual p-chains ending exactly at the prescribed source.
The endpoint is included in the trace but is not a word factor. -/
inductive Trace (a : Pattern) (source : Nat) : Nat → List Nat → Prop
  | stop : Trace a source source [source]
  | next {y z : Nat} {tail : List Nat} :
      source < y → predecessor a y = some z →
      Trace a source z tail → Trace a source y (y :: tail)

/-- Proper marks occupy a step-target position and precede their owner.
Strictly sorted marks provide a canonical representation of their finite set. -/
def Row.ProperMarks (r : Nat) (a : Row) : Prop :=
  a.marks.Pairwise (· < ·) ∧
  ∀ y ∈ a.marks, y < r ∧ ∃ k, a.step ≤ k ∧ a.core[k]? = some y

/-- The source position is read in the owner core, not guessed from the trace. -/
def MarkTrace (a : Pattern) (owner y : Nat) (word : List Nat) : Prop :=
  ∃ row k source, rowAt a owner = some row ∧ y ∈ row.marks ∧
    row.step ≤ k ∧ row.core[k]? = some y ∧
    row.core[k - row.step]? = some source ∧ Trace a source y word

/-- Sat is only a combinatorial condition. It carries no closure theorem. -/
def Sat (a : Pattern) : Prop :=
  ∀ r row, rowAt a r = some row → row.core.length ≤ 2 * row.step →
    ∃ p e er b, row.p = some p ∧ row.e = some e ∧
      rowAt a e = some er ∧ er.b = some b ∧ b ≤ p

theorem row_zero_absent (a : Pattern) : rowAt a 0 = none := by
  simp [rowAt]

theorem trace_nonempty {a : Pattern} {s y : Nat} {xs : List Nat}
    (h : Trace a s y xs) : xs ≠ [] := by
  cases h <;> simp

theorem trace_head {a : Pattern} {s y : Nat} {xs : List Nat}
    (h : Trace a s y xs) : xs.head? = some y := by
  cases h <;> rfl

theorem start_mark_trace : MarkTrace start 4 3 [3, 1] := by
  refine ⟨⟨[0, 1, 2, 3, 4], 2, [3]⟩, 3, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact Trace.next (by decide) (by decide) Trace.stop

end FullMarkedBLP
