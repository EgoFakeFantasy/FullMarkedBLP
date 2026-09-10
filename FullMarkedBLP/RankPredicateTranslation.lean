import FullMarkedBLP.RankSecondOrder

namespace FullMarkedBLP
open FirstOrder Language

def rankPureTermVariable {alpha : Type} : membershipLanguage.Term alpha → alpha
  | .var x => x
  | .func f _ => Empty.elim f

theorem rankPureTermVariable_realize {lambda : Ordinal.{u}} {alpha : Type}
    (term : membershipLanguage.Term alpha) (values : alpha → RankDomain lambda) :
    term.realize values = values (rankPureTermVariable term) := by
  cases term with
  | var => rfl
  | func f _ => exact Empty.elim f

def rankPureLift {alpha : Type} {k n : Nat} (indices : alpha ⊕ Fin k → Fin n) :
    alpha ⊕ Fin (k + 1) → Fin (n + 1) :=
  Sum.elim (fun a => (indices (.inl a)).castSucc)
    (Fin.lastCases (Fin.last n) (fun i => (indices (.inr i)).castSucc))

/-- Translate Mathlib membership formulas into the finite syntax used
for the second-order matrices, without adding any class predicate. -/
def rankPureTranslate {alpha : Type} {k n m : Nat} (phi : membershipLanguage.BoundedFormula alpha k)
    (indices : alpha ⊕ Fin k → Fin n) : RankPredicateFormula m n :=
  match phi with
  | .falsum => .falsum
  | .equal x y => .equal (indices (rankPureTermVariable x)) (indices (rankPureTermVariable y))
  | @BoundedFormula.rel _ _ _ arity relation terms => by
    obtain ⟨same⟩ := relation
    subst arity
    exact .member (indices (rankPureTermVariable (terms 0))) (indices (rankPureTermVariable (terms 1)))
  | .imp p q => .imp (rankPureTranslate p indices) (rankPureTranslate q indices)
  | .all p => .all (rankPureTranslate p (rankPureLift indices))

theorem rankPureTranslate_realize {lambda : Ordinal.{u}} {alpha : Type} {k n m : Nat}
    (phi : membershipLanguage.BoundedFormula alpha k) (indices : alpha ⊕ Fin k → Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda)
    (free : alpha → RankDomain lambda) (bound : Fin k → RankDomain lambda)
    (compatible : ∀ i, values (indices i) = Sum.elim free bound i) :
    (rankPureTranslate phi indices).Realize classes values ↔ phi.Realize free bound := by
  induction phi generalizing n with
  | falsum => rfl
  | equal x y =>
    simp only [rankPureTranslate, RankPredicateFormula.Realize, BoundedFormula.Realize,
      rankPureTermVariable_realize, compatible]
  | @rel k arity relation terms =>
    obtain ⟨same⟩ := relation
    subst arity
    simp only [rankPureTranslate, RankPredicateFormula.Realize, BoundedFormula.Realize,
      Structure.RelMap, rankPureTermVariable_realize, compatible]
  | imp p q ihp ihq =>
    exact imp_congr (ihp indices values bound compatible) (ihq indices values bound compatible)
  | all p ih =>
    apply forall_congr'
    intro x
    apply ih (rankPureLift indices) (Fin.snoc values x) (Fin.snoc bound x)
    intro i
    cases i with
    | inl a => simpa [rankPureLift, Fin.snoc] using compatible (.inl a)
    | inr i =>
      cases i using Fin.lastCases with
      | last => simp [rankPureLift, Fin.snoc]
      | cast i => simpa [rankPureLift, Fin.snoc] using compatible (.inr i)

def rankPredicateOfFormula {m n : Nat} (phi : membershipLanguage.Formula (Fin n)) :
    RankPredicateFormula m n := rankPureTranslate phi (Sum.elim id Fin.elim0)

theorem rankPredicateOfFormula_realize {lambda : Ordinal.{u}} {m n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) :
    (rankPredicateOfFormula phi).Realize classes values ↔ phi.Realize values := by
  apply rankPureTranslate_realize phi _ classes values values Fin.elim0
  intro i
  cases i with
  | inl => rfl
  | inr i => exact Fin.elim0 i

end FullMarkedBLP

