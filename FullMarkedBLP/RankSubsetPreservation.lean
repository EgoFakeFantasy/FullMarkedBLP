import FullMarkedBLP.RankFunctionFormula

namespace FullMarkedBLP
open FirstOrder Language

def rankSubsetFormula : membershipLanguage.Formula (Fin 2) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).imp (rankMemAt (.inr 0) (.inl 1)))

theorem rankSubsetFormula_realize {lambda : Ordinal.{u}} (x y : RankDomain lambda) :
    rankSubsetFormula.Realize ![x, y] ↔ x.val ⊆ y.val := by
  have semantics : rankSubsetFormula.Realize ![x, y] ↔
      ∀ z : RankDomain lambda, z.val ∈ x.val → z.val ∈ y.val := by
    simp [rankSubsetFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, rankMemAt_realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h z hz
    exact h (rankMember x z hz) hz
  · intro h z hz
    exact h hz

theorem rankElementary_subset_iff {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (x y : RankDomain lambda) : (j x).val ⊆ (j y).val ↔ x.val ⊆ y.val := by
  have result := j.map_formula rankSubsetFormula ![x, y]
  have same : j ∘ ![x, y] = ![j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => omega
  rw [same, rankSubsetFormula_realize, rankSubsetFormula_realize] at result
  exact result

end FullMarkedBLP
