import FullMarkedBLP.RankAssignmentFormula

namespace FullMarkedBLP

def rankTableHolds {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) {k : Nat}
    (book : RankDomain lambda) (entries : Fin k → RankDomain lambda) : Prop :=
  (rankTuple hl entries).val ∈ book.val

def rankAssignmentAtCode {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (arityBook code assignment : RankDomain lambda) : Prop :=
  ∃ arity : RankDomain lambda, rankTableHolds hl arityBook ![code, arity] ∧
    ∃ range : RankDomain lambda, rankIsFunction assignment arity range

theorem rankMapPair {alpha beta : Type*} (f : alpha → beta) (x y : alpha) :
    f ∘ ![x, y] = ![f x, f y] := by
  funext i
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => rfl
  | 1 => rfl
  | i + 2 => omega

theorem rankMapSingle {alpha beta : Type*} (f : alpha → beta) (x : alpha) :
    f ∘ ![x] = ![f x] := by
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  subst i
  rfl

theorem rankFormulaValidAssignment_realize_raw {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m n : Nat} (book code assignment : Fin n) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) :
    (rankFormulaValidAssignment book code assignment).Realize classes values ↔
      rankAssignmentAtCode hl (values book) (values code) (values assignment) := by
  simp only [rankFormulaValidAssignment, RankPredicateFormula.realize_ex,
    RankPredicateFormula.realize_and, rankFormulaTupleMem_realize hl,
    rankFormulaAssignment_realize, rankMapPair, Fin.snoc_castSucc, Fin.snoc_last,
    rankAssignmentAtCode, rankTableHolds]

noncomputable def rankSyntaxBooks {lambda : Ordinal.{u}} (hw : Ordinal.omega0 < lambda) :
    Fin 6 → RankDomain lambda :=
  ![rankNatRelation hw rankSyntaxArity, rankNatRelation hw rankSyntaxFalse,
    rankNatRelation hw rankSyntaxEqual, rankNatRelation hw rankSyntaxMember,
    rankNatRelation hw rankSyntaxImp, rankNatRelation hw rankSyntaxAll]

structure RankCodedTruthConditions {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (books : Fin 6 → RankDomain lambda) (truth : RankClass lambda) : Prop where
  falsum : ∀ code assignment, rankAssignmentAtCode hl (books 0) code assignment →
    rankTableHolds hl (books 1) ![code] → ¬ rankTruthHolds hl truth code assignment
  equal : ∀ code assignment i j x y, rankAssignmentAtCode hl (books 0) code assignment →
    rankTableHolds hl (books 2) ![code, i, j] →
    rankGraphApplies assignment i x → rankGraphApplies assignment j y →
    (rankTruthHolds hl truth code assignment ↔ x = y)
  member : ∀ code assignment i j x y, rankAssignmentAtCode hl (books 0) code assignment →
    rankTableHolds hl (books 3) ![code, i, j] →
    rankGraphApplies assignment i x → rankGraphApplies assignment j y →
    (rankTruthHolds hl truth code assignment ↔ x.val ∈ y.val)
  imp : ∀ code assignment p q, rankAssignmentAtCode hl (books 0) code assignment →
    rankTableHolds hl (books 4) ![code, p, q] →
    (rankTruthHolds hl truth code assignment ↔
      (rankTruthHolds hl truth p assignment → rankTruthHolds hl truth q assignment))
  all : ∀ code assignment p arity, rankTableHolds hl (books 0) ![code, arity] →
    (∃ range, rankIsFunction assignment arity range) → rankTableHolds hl (books 5) ![code, p] →
    (rankTruthHolds hl truth code assignment ↔ ∀ x new : RankDomain lambda,
      new.val = assignment.val ∪ {ZFSet.pair arity.val x.val} → rankTruthHolds hl truth p new)

def rankTruthFalseMatrix : RankPredicateFormula 1 6 :=
  let body : RankPredicateFormula 1 8 :=
    .imp (rankFormulaValidAssignment 0 6 7)
      (.imp (rankFormulaTupleMem 1 ![6]) (rankFormulaTruthHolds 0 6 7).not)
  body.all.all

def rankTruthEqualMatrix : RankPredicateFormula 1 6 :=
  let body : RankPredicateFormula 1 12 :=
    .imp (rankFormulaValidAssignment 0 6 7)
      (.imp (rankFormulaTupleMem 2 ![6, 8, 9])
        (.imp (rankFormulaGraphApplies 7 8 10) (.imp (rankFormulaGraphApplies 7 9 11)
          ((rankFormulaTruthHolds 0 6 7).iff (.equal 10 11)))))
  body.all.all.all.all.all.all

def rankTruthMemberMatrix : RankPredicateFormula 1 6 :=
  let body : RankPredicateFormula 1 12 :=
    .imp (rankFormulaValidAssignment 0 6 7)
      (.imp (rankFormulaTupleMem 3 ![6, 8, 9])
        (.imp (rankFormulaGraphApplies 7 8 10) (.imp (rankFormulaGraphApplies 7 9 11)
          ((rankFormulaTruthHolds 0 6 7).iff (.member 10 11)))))
  body.all.all.all.all.all.all

def rankTruthImpMatrix : RankPredicateFormula 1 6 :=
  let body : RankPredicateFormula 1 10 :=
    .imp (rankFormulaValidAssignment 0 6 7) (.imp (rankFormulaTupleMem 4 ![6, 8, 9])
      ((rankFormulaTruthHolds 0 6 7).iff
        (.imp (rankFormulaTruthHolds 0 8 7) (rankFormulaTruthHolds 0 9 7))))
  body.all.all.all.all

def rankTruthAllMatrix : RankPredicateFormula 1 6 :=
  let extension : RankPredicateFormula 1 12 :=
    .imp (rankFormulaAppend 7 11 9 10) (rankFormulaTruthHolds 0 8 11)
  let body : RankPredicateFormula 1 10 :=
    .imp (rankFormulaTupleMem 0 ![6, 9]) (.imp (rankFormulaAssignment 7 9)
      (.imp (rankFormulaTupleMem 5 ![6, 8])
        ((rankFormulaTruthHolds 0 6 7).iff extension.all.all)))
  body.all.all.all.all

/-- One finite matrix, with one class predicate and exactly six set
parameters. The six parameters will be the actual low-rank syntax tables. -/
def rankTruthMatrix : RankPredicateFormula 1 6 :=
  rankTruthFalseMatrix.and (rankTruthEqualMatrix.and (rankTruthMemberMatrix.and
    (rankTruthImpMatrix.and rankTruthAllMatrix)))

theorem rankTruthMatrix_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (books : Fin 6 → RankDomain lambda) (truth : RankClass lambda) :
    rankTruthMatrix.Realize (fun _ => truth) books ↔ RankCodedTruthConditions hl books truth := by
  have hf : rankTruthFalseMatrix.Realize (fun _ => truth) books ↔
      ∀ code assignment, rankAssignmentAtCode hl (books 0) code assignment →
        rankTableHolds hl (books 1) ![code] → ¬ rankTruthHolds hl truth code assignment := by
    simp [rankTruthFalseMatrix, RankPredicateFormula.Realize, RankPredicateFormula.realize_not,
      rankFormulaValidAssignment_realize_raw hl, rankFormulaTupleMem_realize hl,
      rankFormulaTruthHolds_realize hl, rankMapSingle, rankTableHolds, Fin.snoc]
  have he : rankTruthEqualMatrix.Realize (fun _ => truth) books ↔
      ∀ code assignment i j x y, rankAssignmentAtCode hl (books 0) code assignment →
        rankTableHolds hl (books 2) ![code, i, j] →
        rankGraphApplies assignment i x → rankGraphApplies assignment j y →
        (rankTruthHolds hl truth code assignment ↔ x = y) := by
    simp [rankTruthEqualMatrix, RankPredicateFormula.Realize, RankPredicateFormula.realize_iff,
      rankFormulaValidAssignment_realize_raw hl, rankFormulaTupleMem_realize hl,
      rankFormulaTruthHolds_realize hl, rankFormulaGraphApplies_realize, rankMapTriple,
      rankTableHolds, Fin.snoc]
  have hm : rankTruthMemberMatrix.Realize (fun _ => truth) books ↔
      ∀ code assignment i j x y, rankAssignmentAtCode hl (books 0) code assignment →
        rankTableHolds hl (books 3) ![code, i, j] →
        rankGraphApplies assignment i x → rankGraphApplies assignment j y →
        (rankTruthHolds hl truth code assignment ↔ x.val ∈ y.val) := by
    simp [rankTruthMemberMatrix, RankPredicateFormula.Realize, RankPredicateFormula.realize_iff,
      rankFormulaValidAssignment_realize_raw hl, rankFormulaTupleMem_realize hl,
      rankFormulaTruthHolds_realize hl, rankFormulaGraphApplies_realize, rankMapTriple,
      rankTableHolds, Fin.snoc]
  have hi : rankTruthImpMatrix.Realize (fun _ => truth) books ↔
      ∀ code assignment p q, rankAssignmentAtCode hl (books 0) code assignment →
        rankTableHolds hl (books 4) ![code, p, q] →
        (rankTruthHolds hl truth code assignment ↔
          (rankTruthHolds hl truth p assignment → rankTruthHolds hl truth q assignment)) := by
    simp [rankTruthImpMatrix, RankPredicateFormula.Realize, RankPredicateFormula.realize_iff,
      rankFormulaValidAssignment_realize_raw hl, rankFormulaTupleMem_realize hl,
      rankFormulaTruthHolds_realize hl, rankMapTriple, rankTableHolds, Fin.snoc]
  have ha : rankTruthAllMatrix.Realize (fun _ => truth) books ↔
      ∀ code assignment p arity, rankTableHolds hl (books 0) ![code, arity] →
        (∃ range, rankIsFunction assignment arity range) → rankTableHolds hl (books 5) ![code, p] →
        (rankTruthHolds hl truth code assignment ↔ ∀ x new : RankDomain lambda,
          new.val = assignment.val ∪ {ZFSet.pair arity.val x.val} → rankTruthHolds hl truth p new) := by
    simp [rankTruthAllMatrix, RankPredicateFormula.Realize, RankPredicateFormula.realize_iff,
      rankFormulaAssignment_realize, rankFormulaTupleMem_realize hl, rankFormulaAppend_realize hl,
      rankFormulaTruthHolds_realize hl, rankMapPair, rankTableHolds, Fin.snoc]
  rw [rankTruthMatrix, RankPredicateFormula.realize_and, RankPredicateFormula.realize_and,
    RankPredicateFormula.realize_and, RankPredicateFormula.realize_and, hf, he, hm, hi, ha]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.falsum, h.equal, h.member, h.imp, h.all⟩⟩

end FullMarkedBLP
