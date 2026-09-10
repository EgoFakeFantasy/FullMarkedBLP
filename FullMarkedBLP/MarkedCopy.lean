import FullMarkedBLP.Copy
import FullMarkedBLP.TraceCompute

namespace FullMarkedBLP

/-- PDF q is one-based. If idx=q-1 is zero-based, the entry q+1-L
has zero-based index idx+1-L. This is not idx-L. -/
def copyPositionGuard (core : List Nat) (step idx minimum : Nat) : Bool :=
  if step ≤ idx + 1 then (core[idx + 1 - step]?).any (· ≤ minimum) else true

/-- Three trace cases from PDF Definition 10, for short-copy source rows. -/
def copyMarkAllowed (a : Pattern) (source y : Nat)
    (targetCore : List Nat) (targetIdx step : Nat) : Bool :=
  (do
    let last ← a.getLast?
    let minimum ← last.core.head?
    let p ← last.p
    let trace ← computeMarkTrace a source y
    let penultimate ← fromRight trace 2
    if p ≤ penultimate then pure true else do
      let low ← trace.find? (· < p)
      if low < minimum then pure true else do
        let k ← last.core.findIdx? (· == low)
        let shifted ← last.core[k + last.step]?
        pure (last.marks.contains shifted &&
          copyPositionGuard targetCore step targetIdx minimum)).getD false

/-- Marks are selected in target position order; the source is the unique
preimage once strictness of the copy map on legal rows is proved. -/
def copiedRow (a : Pattern) (last : Row) (source : Nat) (row : Row) : Option Row := do
  let core ← copiedCore a.length last source row
  let marked := ((row.core.zip core).zipIdx).filterMap fun ((y, x), idx) =>
    if row.marks.contains y && copyMarkAllowed a source y core idx row.step
    then some x else none
  pure ⟨core, row.step, marked⟩

/-- One original short copy; no native scan is performed here. -/
def shortCopy (a : Pattern) : Option Pattern := do
  if a.length ≤ 2 then none else do
    let last ← a.getLast?
    let sources ← shortCopySources last
    let copied ← sources.mapM fun source => do
      let row ← rowAt a source
      copiedRow a last source row
    pure (a.dropLast ++ copied)

/-- A discriminating regression: the shifted guard must inspect the entry 4,
not the preceding entry 1. This catches the old off-by-one guard. -/
theorem correct_guard_rejects_old_index_example :
    copyPositionGuard [0, 1, 4, 5] 2 3 1 = false := by decide

theorem start_shortCopy : shortCopy start = some
    (zero ++ [⟨[0, 1, 2, 3], 2, []⟩,
      ⟨[0, 1, 2, 3, 4], 2, [3]⟩, ⟨[0, 1, 4, 5], 2, []⟩]) := by decide

end FullMarkedBLP
