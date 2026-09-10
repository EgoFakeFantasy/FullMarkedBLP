import FullMarkedBLP.RankBijectionFormula

namespace FullMarkedBLP
open FirstOrder Language

def rankBijectionAt {alpha : Type} {n : Nat} (f x y : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![f, x, y] rankBijectionFormula

theorem rankBijectionAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (f x y : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankBijectionAt f x y).Realize v xs ↔
      rankIsBijection (Sum.elim v xs f) (Sum.elim v xs x) (Sum.elim v xs y) := by
  rw [rankBijectionAt, BoundedFormula.realize_relabel]
  have he : Sum.elim v (xs ∘ Fin.castAdd 0) ∘ ![f, x, y] =
      ![Sum.elim v xs f, Sum.elim v xs x, Sum.elim v xs y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [he]
  exact rankBijectionFormula_realize _ _ _

def rankEquinumerousFormula : membershipLanguage.Formula (Fin 2) :=
  .ex (rankBijectionAt (.inr 0) (.inl 0) (.inl 1))

theorem rankEquinumerousFormula_realize {lambda : Ordinal.{u}} (x y : RankDomain lambda) :
    rankEquinumerousFormula.Realize ![x, y] ↔ ∃ f : RankDomain lambda, rankIsBijection f x y := by
  simp [rankEquinumerousFormula, Formula.Realize, BoundedFormula.realize_ex,
    rankBijectionAt_realize, Fin.snoc]

theorem rankElementary_card_eq_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (x y : RankDomain lambda) :
    (j x).val.card = (j y).val.card ↔ x.val.card = y.val.card := by
  have hh := j.map_formula rankEquinumerousFormula ![x, y]
  have he : j ∘ ![x, y] = ![j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => omega
  rw [he, rankEquinumerousFormula_realize, rankEquinumerousFormula_realize,
    rankBijection_exists_iff_card_eq hl, rankBijection_exists_iff_card_eq hl] at hh
  exact hh

end FullMarkedBLP
