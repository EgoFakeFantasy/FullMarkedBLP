import FullMarkedBLP.MarkedCopy

namespace FullMarkedBLP

inductive Kind where
  | zero | successor | limit | transient
  deriving DecidableEq, Repr

/-- Ordinary types use full-row lengths 5 and 6, hence core lengths 4 and 5. -/
def classify (a : Pattern) : Kind :=
  if a.length = 2 then .zero else
    match a.getLast? with
    | none => .transient
    | some row =>
      if row.core.take 3 = [0, 1, 2] ∧ row.core.length = 4 then .successor
      else if row.core.take 3 = [0, 1, 2] ∧ row.core.length = 5 ∧ row.step = 3
      then .limit else .transient

def auxiliaryStep (anchor : Nat) (a : Pattern) : Option Pattern :=
  shortCopy (a ++ [⟨[anchor, a.length + 1], 1, []⟩])

/-- The anchor stays fixed throughout E; each stage uses a fresh auxiliary row. -/
def expandFrom (anchor : Nat) (initial : Pattern) : Nat → Option Pattern
  | 0 => some initial
  | k + 1 => (expandFrom anchor initial k).bind (auxiliaryStep anchor)

def expand (a : Pattern) (k : Nat) : Option Pattern := do
  if classify a = .successor ∨ classify a = .limit then do
    let last ← a.getLast?
    let anchor ← last.b
    let initial ← cut a
    expandFrom anchor initial k
  else none

theorem shortCopy_prefix {a b : Pattern} (h : shortCopy a = some b) :
    a.dropLast <+: b := by
  unfold shortCopy at h
  split at h
  next => simp at h
  next =>
    obtain ⟨last, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sources, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨copied, _, h⟩ := Option.bind_eq_some_iff.mp h
    change some (a.dropLast ++ copied) = some b at h
    cases Option.some.inj h
    exact List.prefix_append _ _

theorem auxiliaryStep_prefix {anchor : Nat} {a b : Pattern}
    (h : auxiliaryStep anchor a = some b) : a <+: b := by
  have hh := shortCopy_prefix h
  simpa [List.dropLast_append_cons] using hh

theorem expandFrom_prefix {anchor : Nat} {initial b : Pattern} {k : Nat}
    (h : expandFrom anchor initial k = some b) : initial <+: b := by
  induction k generalizing b with
  | zero =>
    simp [expandFrom] at h
    subst b
    exact List.prefix_refl _
  | succ k ih =>
    obtain ⟨previous, hp, hb⟩ := Option.bind_eq_some_iff.mp h
    exact (ih hp).trans (auxiliaryStep_prefix hb)

#print axioms expandFrom_prefix
end FullMarkedBLP
