import FullMarkedBLP.RankFunctionFormula

namespace FullMarkedBLP
open FirstOrder Language

def rankOntoFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankMemAt (.inr 0) (.inl 2)).imp
    (.ex (rankMemAt (.inr 1) (.inl 1) ⊓ rankGraphAppliesAt (.inl 0) (.inr 1) (.inr 0))))

theorem rankOntoFormula_realize {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankOntoFormula.Realize ![f, x, y] ↔ rankGraphOnto f x y := by
  simp [rankOntoFormula, Formula.Realize, BoundedFormula.Realize,
    rankMemAt_realize, rankGraphAppliesAt_realize, rankGraphOnto, Fin.snoc]

theorem rankElementary_onto_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (f x y : RankDomain lambda) :
    rankGraphOnto (j f) (j x) (j y) ↔ rankGraphOnto f x y := by
  have hh := j.map_formula rankOntoFormula ![f, x, y]
  have he : j ∘ ![f, x, y] = ![j f, j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [he, rankOntoFormula_realize, rankOntoFormula_realize] at hh
  exact hh

end FullMarkedBLP
