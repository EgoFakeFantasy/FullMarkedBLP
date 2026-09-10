import FullMarkedBLP.Native

namespace FullMarkedBLP

abbrev Records := List (Nat × List Nat)

def recordAt (rec : Records) (r : Nat) : Option (List Nat) :=
  ((rec.find? (fun entry => entry.1 == r)).map Prod.snd)

/-- Internal adjacent factors only: the final source endpoint is excluded. -/
def currentPlusOne (a : Pattern) (trace : List Nat) : Bool :=
  let factors := trace.dropLast
  (factors.zip factors.tail).all fun (parent, child) =>
    (rowAt a parent).any (fun row => row.core.contains (child + 1))

def completionRecord (a : Pattern) (rec : Records) (r y : Nat) : Option (List Nat) := do
  let trace ← computeMarkTrace a r y
  let terminalFactor ← fromRight trace 2
  let sources ← recordAt rec terminalFactor
  if sources.isEmpty then none
  else if currentPlusOne a trace then some sources else none

def completeMarkRow (row : Row) (y : Nat) (sources : List Nat) : Row :=
  let targets := (List.range sources.length).map (fun i => y + 1 + i)
  ⟨canonicalColumns (row.core ++ sources ++ targets), row.step + sources.length,
   canonicalColumns (row.marks.filter (fun x => !sources.contains x) ++ targets)⟩

/-- Each frozen mark is checked against the current row and current trace. -/
def completeMark (a : Pattern) (rec : Records) (r y : Nat) : Pattern :=
  match rowAt a r, completionRecord a rec r y with
  | some row, some sources => a.set (r - 1) (completeMarkRow row y sources)
  | _, _ => a

def completeFrozenMarks (a : Pattern) (rec : Records) (r : Nat) : Pattern :=
  match rowAt a r with
  | none => a
  | some row => row.marks.foldl (fun current y => completeMark current rec r y) a

/-- One step consumes exactly one entry row; the new native block is skipped.
The finite bound counts original rows, not the growing current row count. -/
def scanFuel : Nat → Pattern → Records → Nat → Option Pattern
  | 0, a, _, r => if a.length < r then some a else none
  | fuel + 1, a, rec, r =>
    if a.length < r then some a else do
      let marked := completeFrozenMarks a rec r
      let (next, sources) ← native marked r
      let nextRec := if sources.isEmpty then rec else (r, sources) :: rec
      scanFuel fuel next nextRec (r + sources.length + 1)

/-- Full left-to-right scan with an empty initial record, including old prefix. -/
def fullScan (a : Pattern) : Option Pattern := scanFuel a.length a [] 1

def mStar (a : Pattern) : Option Pattern :=
  if classify a = .transient then (shortCopy a).bind fullScan else none

/-- The generation relation will use only positive E parameters. Every
nonzero valid item also has its cut child. -/
inductive Step : Pattern → Pattern → Prop
  | cut {a b} : cut a = some b → Step a b
  | expand {a b k} : 0 < k → expand a k = some b → Step a b
  | marked {a b} : mStar a = some b → Step a b

/-- Literal generated states, including the standard root itself. -/
inductive Generated : Pattern → Prop
  | root : Generated start
  | child {a b} : Generated a → Step a b → Generated b

/-- Checked first full scan; this does not substitute for general closure. -/
def firstChild : Pattern := zero ++
  [⟨[0, 1, 2, 3], 2, []⟩, ⟨[0, 1, 2, 3, 4], 2, [3]⟩,
   ⟨[0, 1, 2, 4, 5], 3, []⟩,
   ⟨[0, 1, 2, 3, 4, 5, 6], 4, [5]⟩,
   ⟨[0, 1, 2, 3, 4, 5, 6, 7], 4, [5, 6]⟩]

theorem start_mStar : mStar start = some firstChild := by decide

theorem firstChild_generated : Generated firstChild :=
  Generated.child Generated.root (Step.marked start_mStar)


end FullMarkedBLP
