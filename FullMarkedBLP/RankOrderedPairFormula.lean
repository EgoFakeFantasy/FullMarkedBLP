import FullMarkedBLP.RankCardinalCharacterization

namespace FullMarkedBLP
open FirstOrder Language

def rankUnorderedPairAt {alpha : Type} {n : Nat} (z x y : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![z, x, y] rankUnorderedPairFormula

theorem rankUnorderedPairAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (z x y : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankUnorderedPairAt z x y).Realize v xs ↔
      rankIsUnorderedPair (Sum.elim v xs z) (Sum.elim v xs x) (Sum.elim v xs y) := by
  classical
  simp [rankUnorderedPairAt, BoundedFormula.realize_relabel, rankUnorderedPairFormula,
    rankIsUnorderedPair, BoundedFormula.Realize, Function.comp_def,
    FirstOrder.Language.Relations.boundedFormula₂, FirstOrder.Language.Relations.boundedFormula,
    Structure.RelMap, Fin.snoc, imp_iff_not_or]

def rankOrderedPairFormula : membershipLanguage.Formula (Fin 3) :=
  .ex (.ex (rankUnorderedPairAt (.inr 0) (.inl 1) (.inl 1) ⊓
    (rankUnorderedPairAt (.inr 1) (.inl 1) (.inl 2) ⊓
      rankUnorderedPairAt (.inl 0) (.inr 0) (.inr 1))))

theorem rankOrderedPairFormula_realize {lambda : Ordinal.{u}} (z x y : RankDomain lambda) :
    rankOrderedPairFormula.Realize ![z, x, y] ↔ rankIsOrderedPair z x y := by
  simp only [rankOrderedPairFormula, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, rankUnorderedPairAt_realize]
  simp [rankIsOrderedPair, Fin.snoc]

end FullMarkedBLP
