import FullMarkedBLP.RankFunctionFormula

namespace FullMarkedBLP
open FirstOrder Language

/-- Strict cofinality of the range of a graph in an ordinal target. -/
def rankGraphCofinal {lambda : Ordinal.{u}} (f x y : RankDomain lambda) : Prop :=
  ∀ b : RankDomain lambda, b.val ∈ y.val →
    ∃ a : RankDomain lambda, a.val ∈ x.val ∧
      ∃ c : RankDomain lambda, c.val ∈ y.val ∧ rankGraphApplies f a c ∧ b.val ∈ c.val

def rankCofinalFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankMemAt (.inr 0) (.inl 2)).imp
    (.ex (rankMemAt (.inr 1) (.inl 1) ⊓
      .ex (rankMemAt (.inr 2) (.inl 2) ⊓
        (rankGraphAppliesAt (.inl 0) (.inr 1) (.inr 2) ⊓
          rankMemAt (.inr 0) (.inr 2))))))

theorem rankCofinalFormula_realize {lambda : Ordinal.{u}} (f x y : RankDomain lambda) :
    rankCofinalFormula.Realize ![f, x, y] ↔ rankGraphCofinal f x y := by
  simp [rankCofinalFormula, Formula.Realize, BoundedFormula.Realize,
    rankMemAt_realize, rankGraphAppliesAt_realize, rankGraphCofinal, Fin.snoc]

theorem rankElementary_cofinal_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (f x y : RankDomain lambda) :
    rankGraphCofinal (j f) (j x) (j y) ↔ rankGraphCofinal f x y := by
  have hh := j.map_formula rankCofinalFormula ![f, x, y]
  have he : j ∘ ![f, x, y] = ![j f, j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [he, rankCofinalFormula_realize, rankCofinalFormula_realize] at hh
  exact hh

end FullMarkedBLP
