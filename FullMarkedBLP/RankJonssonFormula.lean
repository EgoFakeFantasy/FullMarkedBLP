import FullMarkedBLP.RankFunctionSpace
import FullMarkedBLP.RankEquinumerousFormula
import FullMarkedBLP.RankSubsetPreservation

namespace FullMarkedBLP
open FirstOrder Language

def rankSubsetAt {alpha : Type} {n : Nat} (x y : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![x, y] rankSubsetFormula

theorem rankSubsetAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (x y : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankSubsetAt x y).Realize v xs ↔ (Sum.elim v xs x).val ⊆ (Sum.elim v xs y).val := by
  simp only [rankSubsetAt, BoundedFormula.realize_relabel]
  change rankSubsetFormula.Realize (Sum.elim v xs ∘ ![x, y]) ↔ _
  have same : Sum.elim v xs ∘ ![x, y] = ![Sum.elim v xs x, Sum.elim v xs y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => omega
  rw [same]
  exact rankSubsetFormula_realize _ _

/-- The graph formulation of omega-Jonsson: each subset bijective with the
target realizes every target value through a sequence in that subset. -/
def RankGraphOmegaJonsson {lambda : Ordinal.{u}} (color omega target : RankDomain lambda) : Prop :=
  ∀ A : RankDomain lambda, A.val ⊆ target.val →
    ∀ bijection : RankDomain lambda, rankIsBijection bijection target A →
      ∀ value : RankDomain lambda, value.val ∈ target.val →
        ∃ sequence : RankDomain lambda, rankIsFunction sequence omega A ∧ rankGraphApplies color sequence value

def rankJonssonFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankSubsetAt (.inr 0) (.inl 2)).imp
    (.all ((rankBijectionAt (.inr 1) (.inl 2) (.inr 0)).imp
      (.all ((rankMemAt (.inr 2) (.inl 2)).imp
        (.ex ((rankFunctionAt (.inr 3) (.inl 1) (.inr 0)) ⊓
          rankGraphAppliesAt (.inl 0) (.inr 3) (.inr 2))))))))

theorem rankJonssonFormula_realize {lambda : Ordinal.{u}} (color omega target : RankDomain lambda) :
    rankJonssonFormula.Realize ![color, omega, target] ↔ RankGraphOmegaJonsson color omega target := by
  simp [rankJonssonFormula, Formula.Realize, BoundedFormula.Realize,
    rankSubsetAt_realize, rankBijectionAt_realize, rankFunctionAt_realize,
    rankGraphAppliesAt_realize, rankMemAt_realize, RankGraphOmegaJonsson, Fin.snoc]

theorem rankElementary_jonsson_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (color omega target : RankDomain lambda) :
    RankGraphOmegaJonsson (j color) (j omega) (j target) ↔ RankGraphOmegaJonsson color omega target := by
  have result := j.map_formula rankJonssonFormula ![color, omega, target]
  have same : j ∘ ![color, omega, target] = ![j color, j omega, j target] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [same, rankJonssonFormula_realize, rankJonssonFormula_realize] at result
  exact result

end FullMarkedBLP
