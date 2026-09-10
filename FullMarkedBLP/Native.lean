import FullMarkedBLP.Expansion

namespace FullMarkedBLP

/-- Canonical finite sets of column indices, kept as increasing lists. -/
def insertColumn (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys else y :: insertColumn x ys

def canonicalColumns (xs : List Nat) : List Nat := xs.foldr insertColumn []

/-- Native reads B (the penultimate core entry), not the p predecessor. -/
def nativeSourcesFuel (a : Pattern) (p : Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, u => do
    let row ← rowAt a u
    let next ← row.b
    if p < next then do
      let tail ← nativeSourcesFuel a p fuel next
      pure (next :: tail)
    else pure []

/-- Each source transition strictly lowers its row index on valid cores. -/
theorem native_source_lt {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {u v : Nat} {row : Row} (hr : rowAt a u = some row)
    (hb : row.b = some v) : v < u := by
  have hv := valid u row hr
  exact fromRight_lt_last hv.1 hv.2.2.1 (by decide) hb

/-- Source chain for an eligible row. Long rows have no native operation. -/
def nativeSources (a : Pattern) (r : Nat) : Option (List Nat) := do
  let row ← rowAt a r
  if 2 * row.step < row.core.length then pure [] else do
    let p ← row.p
    let e ← row.e
    nativeSourcesFuel a p (e + 1) e

theorem start_native_empty_1 : nativeSources start 1 = some [] := by decide
theorem start_native_empty_3 : nativeSources start 3 = some [] := by decide
theorem start_native_empty_5 : nativeSources start 5 = some [] := by decide

theorem first_copy_native_sources :
    (shortCopy start).bind (fun a => nativeSources a 5) = some [3, 2] := by decide

/-- Earlier columns are fixed; columns to the right of the old owner move. -/
def shiftAfter (r t x : Nat) : Nat := if r < x then x + t else x

def Row.shiftAfter (r t : Nat) (row : Row) : Row :=
  ⟨row.core.map (FullMarkedBLP.shiftAfter r t), row.step,
   row.marks.map (FullMarkedBLP.shiftAfter r t)⟩

/-- Top row of a nonempty native block, at its new owner index r+t. -/
def nativeTop (row : Row) (r : Nat) (sources : List Nat) : Row :=
  let t := sources.length
  let targets := (List.range t).map (fun i => r + 1 + i)
  let marks := (row.marks ++ (List.range t).map (r + ·)).filter
    (fun x => x != r + t && !sources.contains x)
  ⟨canonicalColumns (row.core ++ sources ++ targets), row.step + t,
    canonicalColumns marks⟩

/-- Descend one row of the native block. The medium exception applies only
on the first descent and preserves the step and the source entry. -/
def nativeLower (row : Row) (owner : Nat) (mediumException : Bool) : Option Row := do
  let core := row.core.erase owner
  let marks := row.marks.erase (owner - 1)
  if mediumException then pure ⟨core, row.step, marks⟩ else do
    let source ← row.e
    pure ⟨core.erase source, row.step - 1, marks⟩

/-- Construct bottom-to-top literal order while descending from the top. -/
def nativeBlockDown : Nat → Nat → Bool → Row → Option (List Row)
  | 0, _, _, top => some [top]
  | remaining + 1, owner, medium, top => do
    let lower ← nativeLower top owner medium
    let earlier ← nativeBlockDown remaining (owner - 1) false lower
    pure (earlier ++ [top])

def nativeBlock (row : Row) (r : Nat) (sources : List Nat) : Option (List Row) :=
  if sources.isEmpty then some [row] else
    nativeBlockDown sources.length (r + sources.length)
      (row.core.length == 2 * row.step) (nativeTop row r sources)

/-- Native output and its descending source record. Scanning and record
management are defined separately. -/
def native (a : Pattern) (r : Nat) : Option (Pattern × List Nat) := do
  let row ← rowAt a r
  let sources ← nativeSources a r
  let block ← nativeBlock row r sources
  pure (a.take (r - 1) ++ block ++
    (a.drop r).map (Row.shiftAfter r sources.length), sources)

end FullMarkedBLP
