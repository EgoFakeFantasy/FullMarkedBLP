import FullMarkedBLP.RankSatisfactionClass

namespace FullMarkedBLP
open FirstOrder Language

def rankPredicateAtom {m n k : Nat} (phi : membershipLanguage.Formula (Fin k))
    (indices : Fin k → Fin n) : RankPredicateFormula m n :=
  rankPureTranslate phi (Sum.elim indices Fin.elim0)

theorem rankPredicateAtom_realize {lambda : Ordinal.{u}} {m n k : Nat}
    (phi : membershipLanguage.Formula (Fin k)) (indices : Fin k → Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankPredicateAtom phi indices).Realize classes values ↔ phi.Realize (values ∘ indices) := by
  apply rankPureTranslate_realize phi _ classes values (values ∘ indices) Fin.elim0
  intro i
  cases i with
  | inl => rfl
  | inr i => exact Fin.elim0 i

theorem rankMapTriple {alpha beta : Type*} (f : alpha → beta) (x y z : alpha) :
    f ∘ ![x, y, z] = ![f x, f y, f z] := by
  funext i
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => omega

def rankFormulaOrderedPair {m n : Nat} (p x y : Fin n) : RankPredicateFormula m n :=
  rankPredicateAtom rankOrderedPairFormula ![p, x, y]

theorem rankFormulaOrderedPair_realize {lambda : Ordinal.{u}} {m n : Nat} (p x y : Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaOrderedPair p x y).Realize classes values ↔ rankIsOrderedPair (values p) (values x) (values y) := by
  rw [rankFormulaOrderedPair, rankPredicateAtom_realize, rankMapTriple]
  exact rankOrderedPairFormula_realize _ _ _

def rankFormulaGraphApplies {m n : Nat} (graph x y : Fin n) : RankPredicateFormula m n :=
  rankPredicateAtom rankGraphAppliesFormula ![graph, x, y]

theorem rankFormulaGraphApplies_realize {lambda : Ordinal.{u}} {m n : Nat} (graph x y : Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaGraphApplies graph x y).Realize classes values ↔ rankGraphApplies (values graph) (values x) (values y) := by
  rw [rankFormulaGraphApplies, rankPredicateAtom_realize, rankMapTriple]
  exact rankGraphAppliesFormula_realize _ _ _

def rankFormulaFunction {m n : Nat} (graph domain range : Fin n) : RankPredicateFormula m n :=
  rankPredicateAtom rankFunctionFormula ![graph, domain, range]

theorem rankFormulaFunction_realize {lambda : Ordinal.{u}} {m n : Nat} (graph domain range : Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaFunction graph domain range).Realize classes values ↔
      rankIsFunction (values graph) (values domain) (values range) := by
  rw [rankFormulaFunction, rankPredicateAtom_realize, rankMapTriple]
  exact rankFunctionFormula_realize _ _ _

def rankFormulaAssignment {m n : Nat} (graph domain : Fin n) : RankPredicateFormula m n :=
  (rankFormulaFunction graph.castSucc domain.castSucc (Fin.last n)).ex

theorem rankFormulaAssignment_realize {lambda : Ordinal.{u}} {m n : Nat} (graph domain : Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaAssignment graph domain).Realize classes values ↔
      ∃ range : RankDomain lambda, rankIsFunction (values graph) (values domain) range := by
  simp only [rankFormulaAssignment, RankPredicateFormula.realize_ex, rankFormulaFunction_realize,
    Fin.snoc_castSucc, Fin.snoc_last]

/-- A truth-table query is a genuine first-order formula with one class
predicate; the ordered pair is constructed inside the formula. -/
def rankFormulaTruthHolds {m n : Nat} (truth : Fin m) (code assignment : Fin n) : RankPredicateFormula m n :=
  ((rankFormulaOrderedPair (Fin.last n) code.castSucc assignment.castSucc).and
    (.predicate truth (Fin.last n))).ex

theorem rankFormulaTruthHolds_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m n : Nat} (truth : Fin m) (code assignment : Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaTruthHolds truth code assignment).Realize classes values ↔
      rankTruthHolds hl (classes truth) (values code) (values assignment) := by
  simp only [rankFormulaTruthHolds, RankPredicateFormula.realize_ex, RankPredicateFormula.realize_and,
    rankFormulaOrderedPair_realize, RankPredicateFormula.Realize, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨pair, ordered, member⟩
    have same : pair = rankOrderedPair hl (values code) (values assignment) :=
      Subtype.ext ((rankIsOrderedPair_iff hl _ _ _).mp ordered)
    change classes truth (rankOrderedPair hl (values code) (values assignment))
    exact same ▸ member
  · intro member
    exact ⟨rankOrderedPair hl (values code) (values assignment),
      (rankIsOrderedPair_iff hl _ _ _).mpr rfl, member⟩

end FullMarkedBLP
