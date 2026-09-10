import FullMarkedBLP.RankPairAbsoluteness

namespace FullMarkedBLP
open FirstOrder Language

def rankUnorderedPairFormula : membershipLanguage.Formula (Fin 3) :=
  .all (((show membershipLanguage.Relations 2 from ⟨rfl⟩).boundedFormula₂
    (.var (.inr 0)) (.var (.inl 0))).iff
    ((BoundedFormula.equal (.var (.inr 0)) (.var (.inl 1))) ⊔
      (BoundedFormula.equal (.var (.inr 0)) (.var (.inl 2)))))

theorem rankUnorderedPairFormula_realize {lambda : Ordinal.{u}} (z x y : RankDomain lambda) :
    rankUnorderedPairFormula.Realize ![z, x, y] ↔ rankIsUnorderedPair z x y := by
  classical
  simp [rankUnorderedPairFormula, rankIsUnorderedPair, Formula.Realize, BoundedFormula.Realize,
    FirstOrder.Language.Relations.boundedFormula₂, FirstOrder.Language.Relations.boundedFormula,
    Structure.RelMap, Fin.snoc, imp_iff_not_or]

theorem rankElementary_unorderedPair_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (z x y : RankDomain lambda) :
    (j z).val = {(j x).val, (j y).val} ↔ z.val = {x.val, y.val} := by
  have hh := j.map_formula rankUnorderedPairFormula ![z, x, y]
  have he : j ∘ ![z, x, y] = ![j z, j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [he] at hh
  rw [rankUnorderedPairFormula_realize, rankUnorderedPairFormula_realize,
    rankIsUnorderedPair_iff, rankIsUnorderedPair_iff] at hh
  exact hh

end FullMarkedBLP




