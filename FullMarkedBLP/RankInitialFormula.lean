import FullMarkedBLP.RankEquinumerousFormula

namespace FullMarkedBLP
open FirstOrder Language

def rankEquinumerousAt {alpha : Type} {n : Nat} (x y : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![x, y] rankEquinumerousFormula

theorem rankEquinumerousAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (x y : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankEquinumerousAt x y).Realize v xs ↔
      ∃ f : RankDomain lambda, rankIsBijection f (Sum.elim v xs x) (Sum.elim v xs y) := by
  rw [rankEquinumerousAt, BoundedFormula.realize_relabel]
  have he : Sum.elim v (xs ∘ Fin.castAdd 0) ∘ ![x, y] =
      ![Sum.elim v xs x, Sum.elim v xs y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => omega
  rw [he]
  exact rankEquinumerousFormula_realize _ _

def rankNoMemberBijection {lambda : Ordinal.{u}} (x : RankDomain lambda) : Prop :=
  ∀ a : RankDomain lambda, a.val ∈ x.val → ¬ ∃ f : RankDomain lambda, rankIsBijection f a x

def rankNoMemberBijectionFormula : membershipLanguage.Formula (Fin 1) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).imp (rankEquinumerousAt (.inr 0) (.inl 0)).not)

theorem rankNoMemberBijectionFormula_realize {lambda : Ordinal.{u}} (x : RankDomain lambda) :
    rankNoMemberBijectionFormula.Realize ![x] ↔ rankNoMemberBijection x := by
  simp [rankNoMemberBijectionFormula, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, rankMemAt_realize,
    rankEquinumerousAt_realize, rankNoMemberBijection, Fin.snoc]

theorem rankElementary_noMemberBijection_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) :
    rankNoMemberBijection (j x) ↔ rankNoMemberBijection x := by
  have hh := j.map_formula rankNoMemberBijectionFormula ![x]
  have he : j ∘ ![x] = ![j x] := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  rw [he, rankNoMemberBijectionFormula_realize, rankNoMemberBijectionFormula_realize] at hh
  exact hh

end FullMarkedBLP
