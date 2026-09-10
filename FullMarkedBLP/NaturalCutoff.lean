import FullMarkedBLP.NativeWalkUnique

namespace FullMarkedBLP

/-- Composition is in displayed word order: the head acts last on the argument. -/
def evalWord {α : Type u} (action : Nat → α → α) : List Nat → α → α
  | [], x => x
  | v :: tail, x => action v (evalWord action tail x)

/-- Natural cutoff of a nonempty factor word. The trace endpoint is not a factor. -/
def naturalCutoff {α : Type u} (action : Nat → α → α) (theta : Nat → α) :
    List Nat → Option α
  | [] => none
  | [v] => some (theta (v + 1))
  | v :: w :: tail => (naturalCutoff action theta (w :: tail)).map (action v)

theorem evalWord_append {α : Type u} (action : Nat → α → α)
    (front suffix : List Nat) (x : α) :
    evalWord action (front ++ suffix) x = evalWord action front (evalWord action suffix x) := by
  induction front with
  | nil => rfl
  | cons v tail ih => simp only [List.cons_append, evalWord, ih]

theorem naturalCutoff_snoc {α : Type u} (action : Nat → α → α) (theta : Nat → α)
    (front : List Nat) (terminal : Nat) :
    naturalCutoff action theta (front ++ [terminal]) =
      some (evalWord action front (theta (terminal + 1))) := by
  induction front with
  | nil => rfl
  | cons v tail ih =>
    cases tail with
    | nil => rfl
    | cons w tail => simpa [naturalCutoff, evalWord] using congrArg (Option.map (action v)) ih

theorem naturalCutoff_defined {α : Type u} (action : Nat → α → α) (theta : Nat → α)
    {word : List Nat} (hw : word ≠ []) : ∃ delta, naturalCutoff action theta word = some delta := by
  induction word with
  | nil => contradiction
  | cons v tail ih =>
    cases tail with
    | nil => exact ⟨theta (v + 1), rfl⟩
    | cons w tail =>
      obtain ⟨delta, hd⟩ := ih (by simp)
      exact ⟨action v delta, by simp [naturalCutoff, hd]⟩

/-- This relation deliberately compares membership with both arguments below
    the cutoff; equality of the functions' values is not part of the definition. -/
def cutoffAgreement {V : Type u} {O : Type v}
    (mem : V → V → Prop) (below : O → V → Prop)
    (delta : O) (f g : V → V) : Prop :=
  ∀ x z, below delta x → below delta z → (mem x (f z) ↔ mem x (g z))

theorem cutoffAgreement_refl {V : Type u} {O : Type v}
    (mem : V → V → Prop) (below : O → V → Prop) (delta : O) (f : V → V) :
    cutoffAgreement mem below delta f f := by
  intro x z hx hz
  rfl

theorem cutoffAgreement_symm {V : Type u} {O : Type v}
    {mem : V → V → Prop} {below : O → V → Prop} {delta : O} {f g : V → V}
    (h : cutoffAgreement mem below delta f g) : cutoffAgreement mem below delta g f := by
  intro x z hx hz
  exact (h x z hx hz).symm

theorem cutoffAgreement_trans {V : Type u} {O : Type v}
    {mem : V → V → Prop} {below : O → V → Prop} {delta : O} {f g h : V → V}
    (hfg : cutoffAgreement mem below delta f g) (hgh : cutoffAgreement mem below delta g h) :
    cutoffAgreement mem below delta f h := by
  intro x z hx hz
  exact (hfg x z hx hz).trans (hgh x z hx hz)

theorem cutoffAgreement_restrict {V : Type u} {O : Type v}
    {mem : V → V → Prop} {below : O → V → Prop} {delta epsilon : O} {f g : V → V}
    (hsub : ∀ x, below epsilon x → below delta x)
    (h : cutoffAgreement mem below delta f g) : cutoffAgreement mem below epsilon f g := by
  intro x z hx hz
  exact h x z (hsub x hx) (hsub z hz)

/-- The cutoff interval follows from the two adjacent-column bounds for each
    factor edge. These hypotheses must later be obtained from actual BLS rows. -/
theorem naturalCutoff_bounds {α : Type u}
    (lt le : α → α → Prop) (action : Nat → α → α) (theta : Nat → α)
    (leRefl : ∀ x, le x x) (leTrans : ∀ {x y z}, le x y → le y z → le x z)
    (strict : ∀ v x y, lt x y → lt (action v x) (action v y))
    (mono : ∀ v x y, le x y → le (action v x) (action v y))
    (successor : ∀ v, lt (theta v) (theta (v + 1)))
    (v : Nat) (tail : List Nat)
    (edges : ∀ parent child, (parent, child) ∈ (v :: tail).zip tail →
      action parent (theta child) = theta parent ∧
      le (action parent (theta (child + 1))) (theta (parent + 1)))
    {delta : α} (hd : naturalCutoff action theta (v :: tail) = some delta) :
    lt (theta v) delta ∧ le delta (theta (v + 1)) := by
  induction tail generalizing v delta with
  | nil =>
    have he : theta (v + 1) = delta := Option.some.inj hd
    subst delta
    exact ⟨successor v, leRefl _⟩
  | cons w tail ih =>
    obtain ⟨epsilon, he⟩ := naturalCutoff_defined action theta (word := w :: tail) (by simp)
    have hdelta : action v epsilon = delta := by
      simpa [naturalCutoff, he] using hd
    have hedge := edges v w (by simp)
    have htail := ih w (fun parent child hm => edges parent child (by simp [hm])) he
    constructor
    · have hlow := strict v _ _ htail.1
      simpa only [hedge.1, hdelta] using hlow
    · have hhigh := leTrans (mono v _ _ htail.2) hedge.2
      simpa only [hdelta] using hhigh

theorem naturalCutoff_exact_of_successor_edges {α : Type u}
    (action : Nat → α → α) (theta : Nat → α) (v : Nat) (tail : List Nat)
    (edges : ∀ parent child, (parent, child) ∈ (v :: tail).zip tail →
      action parent (theta (child + 1)) = theta (parent + 1)) :
    naturalCutoff action theta (v :: tail) = some (theta (v + 1)) := by
  induction tail generalizing v with
  | nil => rfl
  | cons w tail ih =>
    have ht := ih w (fun parent child hm => edges parent child (by simp [hm]))
    have he := edges v w (by simp)
    simp [naturalCutoff, ht, he]

end FullMarkedBLP



