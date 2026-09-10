import FullMarkedBLP.RankGraphFormula

namespace FullMarkedBLP
open FirstOrder Language

def rankGraphBetweenFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).imp
    (.ex (.ex (rankMemAt (.inr 1) (.inl 1) ⊓
      (rankMemAt (.inr 2) (.inl 2) ⊓ rankOrderedPairAt (.inr 0) (.inr 1) (.inr 2))))))

theorem rankGraphBetweenFormula_realize {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankGraphBetweenFormula.Realize ![f, x, y] ↔ rankGraphBetween f x y := by
  simp [rankGraphBetweenFormula, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    rankMemAt_realize, rankOrderedPairAt_realize, rankGraphBetween, Fin.snoc]

theorem rankElementary_graphBetween_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (f x y : RankDomain lambda) :
    rankGraphBetween (j f) (j x) (j y) ↔ rankGraphBetween f x y := by
  have hh := j.map_formula rankGraphBetweenFormula ![f, x, y]
  have he : j ∘ ![f, x, y] = ![j f, j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [he, rankGraphBetweenFormula_realize, rankGraphBetweenFormula_realize] at hh
  exact hh

end FullMarkedBLP
