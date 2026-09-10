import FullMarkedBLP.RankSecondOrder

namespace FullMarkedBLP.RankPredicateFormula

def liftSetIndices {n t : Nat} (indices : Fin n → Fin t) : Fin (n + 1) → Fin (t + 1) :=
  Fin.lastCases (Fin.last t) (fun i => (indices i).castSucc)

def relabelSets {m n t : Nat} (p : RankPredicateFormula m n)
    (indices : Fin n → Fin t) : RankPredicateFormula m t :=
  match p with
  | .falsum => .falsum
  | .equal x y => .equal (indices x) (indices y)
  | .member x y => .member (indices x) (indices y)
  | .predicate a x => .predicate a (indices x)
  | .imp p q => .imp (p.relabelSets indices) (q.relabelSets indices)
  | .all p => .all (p.relabelSets (liftSetIndices indices))

theorem realize_relabelSets {lambda : Ordinal.{u}} {m n t : Nat}
    (p : RankPredicateFormula m n) (indices : Fin n → Fin t)
    (classes : Fin m → RankClass lambda) (values : Fin t → RankDomain lambda) :
    (p.relabelSets indices).Realize classes values ↔ p.Realize classes (values ∘ indices) := by
  induction p generalizing t with
  | falsum => rfl
  | equal => rfl
  | member => rfl
  | predicate => rfl
  | imp p q ihp ihq => exact imp_congr (ihp indices values) (ihq indices values)
  | all p ih =>
    change (∀ x, (p.relabelSets (liftSetIndices indices)).Realize classes (Fin.snoc values x)) ↔ _
    apply forall_congr'
    intro x
    have compatible : Fin.snoc values x ∘ liftSetIndices indices = Fin.snoc (values ∘ indices) x := by
      funext i
      cases i using Fin.lastCases with
      | last => simp [liftSetIndices]
      | cast i => simp [liftSetIndices]
    rw [ih, compatible]

end FullMarkedBLP.RankPredicateFormula
