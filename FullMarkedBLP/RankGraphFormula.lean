import FullMarkedBLP.RankOrderedPairFormula

namespace FullMarkedBLP
open FirstOrder Language

def rankMemAt {alpha : Type} {n : Nat} (x y : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  (show membershipLanguage.Relations 2 from ⟨rfl⟩).boundedFormula₂ (.var x) (.var y)

theorem rankMemAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (x y : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankMemAt x y).Realize v xs ↔ (Sum.elim v xs x).val ∈ (Sum.elim v xs y).val := by
  simp [rankMemAt, BoundedFormula.Realize, FirstOrder.Language.Relations.boundedFormula₂,
    FirstOrder.Language.Relations.boundedFormula, Structure.RelMap]

def rankOrderedPairAt {alpha : Type} {n : Nat} (z x y : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![z, x, y] rankOrderedPairFormula

theorem rankOrderedPairAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (z x y : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankOrderedPairAt z x y).Realize v xs ↔
      rankIsOrderedPair (Sum.elim v xs z) (Sum.elim v xs x) (Sum.elim v xs y) := by
  simp [rankOrderedPairAt, BoundedFormula.realize_relabel, rankOrderedPairFormula,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, rankUnorderedPairAt_realize,
    rankIsOrderedPair, Function.comp_def, Fin.snoc]
  have he : (fun i : Fin n => xs (((Fin.castAdd 2 i).castLT (n := n + 1) (i.isLt.trans_le (Nat.le_succ n))).castLT i.isLt)) = xs := by
    funext i
    congr 1
  simpa only [he]

def rankGraphAppliesFormula : membershipLanguage.Formula (Fin 3) :=
  .ex (rankMemAt (.inr 0) (.inl 0) ⊓ rankOrderedPairAt (.inr 0) (.inl 1) (.inl 2))

theorem rankGraphAppliesFormula_realize {lambda : Ordinal.{u}} (f a b : RankDomain lambda) :
    rankGraphAppliesFormula.Realize ![f, a, b] ↔ rankGraphApplies f a b := by
  simp [rankGraphAppliesFormula, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, rankMemAt_realize, rankOrderedPairAt_realize,
    rankGraphApplies, Fin.snoc]

end FullMarkedBLP



