import FullMarkedBLP.RankPredicateTranslation

namespace FullMarkedBLP
open FirstOrder Language

def rankPredicateOldLift {alpha : Type} {n k : Nat} (indices : Fin n → alpha ⊕ Fin k) :
    Fin (n + 1) → alpha ⊕ Fin (k + 1) :=
  Fin.lastCases (.inr (Fin.last k)) (fun i => Sum.map id Fin.castSucc (indices i))

/-- The pure fragment of the class-matrix syntax translates back to
Mathlib first-order syntax. No surjectivity of an embedding is used. -/
def rankPredicatePureTranslate {alpha : Type} {n k : Nat} (phi : RankPredicateFormula 0 n)
    (indices : Fin n → alpha ⊕ Fin k) : membershipLanguage.BoundedFormula alpha k :=
  match phi with
  | .falsum => .falsum
  | .equal x y => .equal (.var (indices x)) (.var (indices y))
  | .member x y => rankMemAt (indices x) (indices y)
  | .predicate a _ => Fin.elim0 a
  | .imp p q => .imp (rankPredicatePureTranslate p indices) (rankPredicatePureTranslate q indices)
  | .all p => .all (rankPredicatePureTranslate p (rankPredicateOldLift indices))

theorem rankPredicatePureTranslate_realize {lambda : Ordinal.{u}} {alpha : Type} {n k : Nat}
    (phi : RankPredicateFormula 0 n) (indices : Fin n → alpha ⊕ Fin k)
    (values : Fin n → RankDomain lambda) (free : alpha → RankDomain lambda)
    (bound : Fin k → RankDomain lambda)
    (compatible : ∀ i, values i = Sum.elim free bound (indices i)) :
    phi.Realize Fin.elim0 values ↔ (rankPredicatePureTranslate phi indices).Realize free bound := by
  induction phi generalizing k with
  | falsum => rfl
  | equal x y =>
    change values x = values y ↔ Sum.elim free bound (indices x) = Sum.elim free bound (indices y)
    rw [compatible, compatible]
  | member x y =>
    rw [rankPredicatePureTranslate, rankMemAt_realize]
    change (values x).val ∈ (values y).val ↔ _
    rw [compatible, compatible]
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq => exact imp_congr (ihp indices values bound compatible) (ihq indices values bound compatible)
  | all p ih =>
    change (∀ x, p.Realize Fin.elim0 (Fin.snoc values x)) ↔
      ∀ x, (rankPredicatePureTranslate p (rankPredicateOldLift indices)).Realize free (Fin.snoc bound x)
    apply forall_congr'
    intro x
    apply ih (rankPredicateOldLift indices) (Fin.snoc values x) (Fin.snoc bound x)
    intro i
    cases i using Fin.lastCases with
    | last => simp [rankPredicateOldLift]
    | cast i =>
      cases hi : indices i with
      | inl a => simpa [rankPredicateOldLift, hi] using compatible i
      | inr b => simpa [rankPredicateOldLift, hi] using compatible i

def rankPredicateToFormula {n : Nat} (phi : RankPredicateFormula 0 n) :
    membershipLanguage.Formula (Fin n) := rankPredicatePureTranslate phi Sum.inl

theorem rankPredicateToFormula_realize {lambda : Ordinal.{u}} {n : Nat}
    (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda) :
    phi.Realize Fin.elim0 values ↔ (rankPredicateToFormula phi).Realize values :=
  rankPredicatePureTranslate_realize phi Sum.inl values values Fin.elim0 (fun _ => rfl)

theorem rankPredicate_elementary {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    {n : Nat} (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda) :
    phi.Realize Fin.elim0 (j ∘ values) ↔ phi.Realize Fin.elim0 values := by
  rw [rankPredicateToFormula_realize, rankPredicateToFormula_realize]
  exact j.map_formula _ values

end FullMarkedBLP
