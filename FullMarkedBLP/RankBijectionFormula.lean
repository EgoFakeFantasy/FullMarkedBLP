import FullMarkedBLP.RankOntoFormula

namespace FullMarkedBLP
open FirstOrder Language

def rankOneToOneFormula : membershipLanguage.Formula (Fin 3) :=
  .all (.all (.all ((rankMemAt (.inr 0) (.inl 1)).imp
    ((rankMemAt (.inr 1) (.inl 1)).imp
      ((rankGraphAppliesAt (.inl 0) (.inr 0) (.inr 2)).imp
        ((rankGraphAppliesAt (.inl 0) (.inr 1) (.inr 2)).imp
          (.equal (.var (.inr 0)) (.var (.inr 1)))))))))

theorem rankOneToOneFormula_realize {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankOneToOneFormula.Realize ![f, x, y] ↔ rankGraphOneToOne f x := by
  simp [rankOneToOneFormula, Formula.Realize, BoundedFormula.Realize,
    rankMemAt_realize, rankGraphAppliesAt_realize, rankGraphOneToOne, Fin.snoc]

def rankBijectionFormula : membershipLanguage.Formula (Fin 3) :=
  rankFunctionFormula ⊓ (rankOntoFormula ⊓ rankOneToOneFormula)

theorem rankBijectionFormula_realize {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankBijectionFormula.Realize ![f, x, y] ↔ rankIsBijection f x y := by
  simp only [rankBijectionFormula, Formula.Realize, BoundedFormula.realize_inf]
  change (rankFunctionFormula.Realize ![f, x, y] ∧
    rankOntoFormula.Realize ![f, x, y] ∧ rankOneToOneFormula.Realize ![f, x, y]) ↔ _
  rw [rankFunctionFormula_realize, rankOntoFormula_realize, rankOneToOneFormula_realize]
  rfl

theorem rankElementary_bijection_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (f x y : RankDomain lambda) :
    rankIsBijection (j f) (j x) (j y) ↔ rankIsBijection f x y := by
  have hh := j.map_formula rankBijectionFormula ![f, x, y]
  have he : j ∘ ![f, x, y] = ![j f, j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [he, rankBijectionFormula_realize, rankBijectionFormula_realize] at hh
  exact hh

end FullMarkedBLP

