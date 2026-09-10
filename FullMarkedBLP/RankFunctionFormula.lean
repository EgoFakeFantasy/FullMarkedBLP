import FullMarkedBLP.RankGraphBetweenFormula

namespace FullMarkedBLP
open FirstOrder Language

def rankGraphAppliesAt {alpha : Type} {n : Nat} (f a b : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![f, a, b] rankGraphAppliesFormula

theorem rankGraphAppliesAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (f a b : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankGraphAppliesAt f a b).Realize v xs ↔
      rankGraphApplies (Sum.elim v xs f) (Sum.elim v xs a) (Sum.elim v xs b) := by
  simp [rankGraphAppliesAt, BoundedFormula.realize_relabel, rankGraphAppliesFormula,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, rankMemAt_realize,
    rankOrderedPairAt_realize, rankGraphApplies, Function.comp_def, Fin.snoc]

def rankFunctionTotalFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankMemAt (.inr 0) (.inl 1)).imp
    (.ex (rankMemAt (.inr 1) (.inl 2) ⊓
      (rankGraphAppliesAt (.inl 0) (.inr 0) (.inr 1) ⊓
        .all ((rankGraphAppliesAt (.inl 0) (.inr 0) (.inr 2)).imp
          (.equal (.var (.inr 2)) (.var (.inr 1))))))))

def rankFunctionFormula : membershipLanguage.Formula (Fin 3) :=
  rankGraphBetweenFormula ⊓ rankFunctionTotalFormula

theorem rankFunctionFormula_realize {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankFunctionFormula.Realize ![f, x, y] ↔ rankIsFunction f x y := by
  simp only [rankFunctionFormula, Formula.Realize, BoundedFormula.realize_inf]
  change (rankGraphBetweenFormula.Realize ![f, x, y] ∧ rankFunctionTotalFormula.Realize ![f, x, y]) ↔ _
  rw [show rankGraphBetweenFormula.Realize ![f, x, y] ↔ rankGraphBetween f x y from
    rankGraphBetweenFormula_realize f x y]
  simp [Formula.Realize, rankFunctionTotalFormula, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.Realize,
    rankMemAt_realize, rankGraphAppliesAt_realize, rankIsFunction, Fin.snoc]

theorem rankElementary_function_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (f x y : RankDomain lambda) :
    rankIsFunction (j f) (j x) (j y) ↔ rankIsFunction f x y := by
  have hh := j.map_formula rankFunctionFormula ![f, x, y]
  have he : j ∘ ![f, x, y] = ![j f, j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [he, rankFunctionFormula_realize, rankFunctionFormula_realize] at hh
  exact hh

end FullMarkedBLP



