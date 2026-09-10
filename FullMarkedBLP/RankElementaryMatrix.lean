import FullMarkedBLP.RankAssignmentMap
import FullMarkedBLP.RankPredicatePureFormula

namespace FullMarkedBLP

def rankPreservesCodedTruth {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (arityBook : RankDomain lambda) (graph truth : RankClass lambda) : Prop :=
  ∀ code source target, rankAssignmentAtCode hl arityBook code source →
    rankAssignmentAtCode hl arityBook code target → rankAssignmentMapped hl graph source target →
    (rankTruthHolds hl truth code source ↔ rankTruthHolds hl truth code target)

def rankPreservesTruthMatrix : RankPredicateFormula 2 6 :=
  let body : RankPredicateFormula 2 9 :=
    .imp (rankFormulaValidAssignment 0 6 7) (.imp (rankFormulaValidAssignment 0 6 8)
      (.imp (rankFormulaAssignmentMapped 0 7 8)
        ((rankFormulaTruthHolds 1 6 7).iff (rankFormulaTruthHolds 1 6 8))))
  body.all.all.all

theorem rankPreservesTruthMatrix_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (books : Fin 6 → RankDomain lambda) (graph truth : RankClass lambda) :
    rankPreservesTruthMatrix.Realize ![graph, truth] books ↔
      rankPreservesCodedTruth hl (books 0) graph truth := by
  simp [rankPreservesTruthMatrix, RankPredicateFormula.Realize, RankPredicateFormula.realize_iff,
    rankFormulaValidAssignment_realize_raw hl, rankFormulaAssignmentMapped_realize hl,
    rankFormulaTruthHolds_realize hl, rankPreservesCodedTruth, Fin.snoc]

def rankElementaryMatrix : RankPredicateFormula 2 6 :=
  ((rankClassFunctionMatrix.relabelClasses (fun _ => (0 : Fin 2))).relabelSets Fin.elim0).and
    ((rankTruthMatrix.relabelClasses (fun _ => (1 : Fin 2))).and rankPreservesTruthMatrix)

structure RankClassElementaryConditions {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (graph truth : RankClass lambda) : Prop where
  function : RankClassFunction hl graph
  truthConditions : RankTruthConditions hl truth
  preserves : rankPreservesCodedTruth hl (rankSyntaxBooks hw 0) graph truth

theorem rankElementaryMatrix_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (graph truth : RankClass lambda) :
    rankElementaryMatrix.Realize ![graph, truth] (rankSyntaxBooks hw) ↔
      RankClassElementaryConditions hl hw graph truth := by
  simp only [rankElementaryMatrix, RankPredicateFormula.realize_and,
    RankPredicateFormula.realize_relabelSets, RankPredicateFormula.realize_relabelClasses]
  have empty : rankSyntaxBooks hw ∘ (Fin.elim0 : Fin 0 → Fin 6) = Fin.elim0 := Subsingleton.elim _ _
  rw [empty]
  change (rankClassFunctionMatrix.Realize (fun _ => graph) Fin.elim0 ∧
    rankTruthMatrix.Realize (fun _ => truth) (rankSyntaxBooks hw) ∧
    rankPreservesTruthMatrix.Realize ![graph, truth] (rankSyntaxBooks hw)) ↔ _
  rw [rankClassFunctionMatrix_realize hl, rankTruthMatrix_correct hl hw, rankPreservesTruthMatrix_realize hl]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.function, h.truthConditions, h.preserves⟩⟩

/-- Extract an actual Mathlib elementary embedding from the finite coded
truth-preservation condition. Every first-order formula is covered. -/
noncomputable def RankClassElementaryConditions.embedding {lambda : Ordinal.{u}}
    {hl : Order.IsSuccLimit lambda} {hw : Ordinal.omega0 < lambda} {graph truth : RankClass lambda}
    (conditions : RankClassElementaryConditions hl hw graph truth) : RankElementaryEmbedding lambda where
  toFun := conditions.function.map
  map_formula' := by
    intro n phi values
    let p : RankPredicateFormula 0 n := rankPredicateOfFormula phi
    have comparison := conditions.preserves _ _ _ (rankAssignmentAtCode_formula hl hw p values)
      (rankAssignmentAtCode_formula hl hw p (conditions.function.map ∘ values))
      (rankAssignmentMapped_map conditions.function values)
    change rankFormulaTruth hl truth p values ↔
      rankFormulaTruth hl truth p (conditions.function.map ∘ values) at comparison
    have pure := (conditions.truthConditions.realize p (conditions.function.map ∘ values)).symm.trans
      (comparison.symm.trans (conditions.truthConditions.realize p values))
    dsimp only [p] at pure
    rw [rankPredicateOfFormula_realize, rankPredicateOfFormula_realize] at pure
    exact pure

theorem RankClassElementaryConditions.embedding_graph {lambda : Ordinal.{u}}
    {hl : Order.IsSuccLimit lambda} {hw : Ordinal.omega0 < lambda} {graph truth : RankClass lambda}
    (conditions : RankClassElementaryConditions hl hw graph truth) :
    rankEmbeddingClassGraph conditions.embedding = graph := by
  rw [← rankFunctionClassGraph_embedding hl]
  change rankFunctionClassGraph hl conditions.function.map = graph
  exact conditions.function.graph_map

theorem rankAssignmentMapped_embedding_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) {n : Nat} (source target : Fin n → RankDomain lambda) :
    rankAssignmentMapped hl (rankEmbeddingClassGraph j) (rankAssignment hl source) (rankAssignment hl target) ↔
      target = j ∘ source := by
  let function := rankFunctionClassGraph_function hl j
  have same : function.map = j := by
    funext x
    exact ((rankFunctionClassGraph_pair hl j x _).mp (function.map_spec x)).symm
  have result := rankAssignmentMapped_iff function source target
  rw [same, rankFunctionClassGraph_embedding hl] at result
  exact result

theorem rankElementary_codedConditions {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (j : RankElementaryEmbedding lambda) :
    RankClassElementaryConditions hl hw (rankEmbeddingClassGraph j) (rankSatisfaction hl) := by
  constructor
  · rw [← rankFunctionClassGraph_embedding hl]
    exact rankFunctionClassGraph_function hl j
  · exact rankSatisfaction_conditions hl
  · intro code source target sourceValid targetValid mapped
    obtain ⟨n, phi, values, rfl, rfl⟩ := (rankAssignmentAtCode_iff hl hw _ _).mp sourceValid
    obtain ⟨other, rfl⟩ := (rankValidAssignment_formula_iff hl phi target).mp
      ((rankAssignmentAtCode_iff hl hw _ _).mp targetValid)
    have same := (rankAssignmentMapped_embedding_iff hl j values other).mp mapped
    rw [same]
    change rankFormulaTruth hl (rankSatisfaction hl) phi values ↔
      rankFormulaTruth hl (rankSatisfaction hl) phi (j ∘ values)
    rw [rankSatisfaction_realize, rankSatisfaction_realize]
    exact (rankPredicate_elementary j phi values).symm

theorem rankElementary_matrix {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (j : RankElementaryEmbedding lambda) :
    rankElementaryMatrix.Realize ![rankEmbeddingClassGraph j, rankSatisfaction hl] (rankSyntaxBooks hw) :=
  (rankElementaryMatrix_realize hl hw _ _).mpr (rankElementary_codedConditions hl hw j)

/-- Exact finite existential-class description of elementary-embedding
graphs, on ALL classes, using only the six actual syntax-table parameters. -/
theorem rankElementaryGraph_sigmaOne {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (graph : RankClass lambda) :
    rankSigmaOneSatisfies (p := 1) rankElementaryMatrix (fun _ : Fin 1 => graph) (rankSyntaxBooks hw) ↔
      ∃ j : RankElementaryEmbedding lambda, rankEmbeddingClassGraph j = graph := by
  have appended (witness : Fin 1 → RankClass lambda) :
      Fin.append (fun _ : Fin 1 => graph) witness = ![graph, witness 0] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | i + 2 => omega
  constructor
  · rintro ⟨witness, matrix⟩
    rw [appended] at matrix
    let conditions := (rankElementaryMatrix_realize hl hw graph (witness 0)).mp matrix
    exact ⟨conditions.embedding, conditions.embedding_graph⟩
  · rintro ⟨j, rfl⟩
    refine ⟨fun _ => rankSatisfaction hl, ?_⟩
    rw [appended]
    exact rankElementary_matrix hl hw j

end FullMarkedBLP
