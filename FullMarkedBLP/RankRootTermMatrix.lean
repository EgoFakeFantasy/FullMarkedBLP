import FullMarkedBLP.RankFiniteClassFormula

namespace FullMarkedBLP

/-- A finite block of application equations. The explicit powers include
P_0, which is constrained to equal the root graph. -/
def rankRootTermMatrix (k : Nat) {m : Nat} (root truth output : Fin m)
    (powers : Fin (k + 1) → Fin m) : RankPredicateFormula m 6 :=
  (rankElementaryMatrix.relabelClasses ![root, truth]).and
    ((rankFormulaNontrivial root).and
      ((rankFormulaClassEqual (powers 0) root).and
        ((rankFormulaFiniteAnd (fun i : Fin k => rankFormulaClassImage root (powers i.castSucc) (powers i.succ))).and
          (rankFormulaClassImage (powers (Fin.last k)) root output))))

theorem rankRootTermMatrix_sound {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (k : Nat) {m : Nat} (root truth output : Fin m)
    (powers : Fin (k + 1) → Fin m) (classes : Fin m → RankClass lambda)
    (matrix : (rankRootTermMatrix k root truth output powers).Realize classes (rankSyntaxBooks hw)) :
    RankRootExists hl k (classes output) := by
  simp only [rankRootTermMatrix, RankPredicateFormula.realize_and] at matrix
  obtain ⟨elementary, nontrivial, initial, steps, finalStep⟩ := matrix
  rw [RankPredicateFormula.realize_relabelClasses, rankMapPair] at elementary
  let conditions := (rankElementaryMatrix_realize hl hw _ _).mp elementary
  let j := conditions.embedding
  have rootGraph : classes root = rankEmbeddingClassGraph j := conditions.embedding_graph.symm
  obtain ⟨critical, cp⟩ := (rankFormulaNontrivial_realize hl root classes (rankSyntaxBooks hw) j rootGraph).mp nontrivial
  have initialGraph := (rankFormulaClassEqual_realize (powers 0) root classes (rankSyntaxBooks hw)).mp initial
  have stepGraphs := (rankFormulaFiniteAnd_realize _ classes (rankSyntaxBooks hw)).mp steps
  have powerGraphs : ∀ (i : Nat) (hi : i ≤ k),
      classes (powers ⟨i, Nat.lt_succ_of_le hi⟩) = rankEmbeddingClassGraph (rankCriticalSequenceEmbedding hl j i) := by
    intro i
    induction i with
    | zero => intro hi; exact initialGraph.trans rootGraph
    | succ i ih =>
      intro hi
      let index : Fin k := ⟨i, by omega⟩
      have imageEq := (rankFormulaClassImage_realize hl root (powers index.castSucc) (powers index.succ)
        classes (rankSyntaxBooks hw) j rootGraph).mp (stepGraphs index)
      have previous : classes (powers index.castSucc) = rankEmbeddingClassGraph (rankCriticalSequenceEmbedding hl j i) :=
        ih (by omega)
      rw [previous, rankClassImage_embeddingGraph hl] at imageEq
      exact imageEq
  have finalEq := (rankFormulaClassImage_realize hl (powers (Fin.last k)) root output
    classes (rankSyntaxBooks hw) (rankCriticalSequenceEmbedding hl j k) (powerGraphs k le_rfl)).mp finalStep
  rw [rootGraph, rankClassImage_embeddingGraph hl] at finalEq
  exact ⟨j, critical, cp, finalEq.symm⟩

theorem rankRootTermMatrix_complete {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (k : Nat) {m : Nat} (root truth output : Fin m)
    (powers : Fin (k + 1) → Fin m) (classes : Fin m → RankClass lambda)
    (j : RankElementaryEmbedding lambda) {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (rootGraph : classes root = rankEmbeddingClassGraph j) (truthClass : classes truth = rankSatisfaction hl)
    (powerGraphs : ∀ i, classes (powers i) = rankEmbeddingClassGraph (rankCriticalSequenceEmbedding hl j i.val))
    (outputGraph : classes output = rankEmbeddingClassGraph (rankApply hl (rankCriticalSequenceEmbedding hl j k) j)) :
    (rankRootTermMatrix k root truth output powers).Realize classes (rankSyntaxBooks hw) := by
  simp only [rankRootTermMatrix, RankPredicateFormula.realize_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [RankPredicateFormula.realize_relabelClasses, rankMapPair, rootGraph, truthClass]
    exact rankElementary_matrix hl hw j
  · exact (rankFormulaNontrivial_realize hl root classes (rankSyntaxBooks hw) j rootGraph).mpr ⟨critical, cp⟩
  · apply (rankFormulaClassEqual_realize (powers 0) root classes (rankSyntaxBooks hw)).mpr
    exact (powerGraphs 0).trans rootGraph.symm
  · apply (rankFormulaFiniteAnd_realize _ classes (rankSyntaxBooks hw)).mpr
    intro i
    apply (rankFormulaClassImage_realize hl root (powers i.castSucc) (powers i.succ)
      classes (rankSyntaxBooks hw) j rootGraph).mpr
    rw [powerGraphs, powerGraphs, rankClassImage_embeddingGraph hl]
    rfl
  · apply (rankFormulaClassImage_realize hl (powers (Fin.last k)) root output classes
      (rankSyntaxBooks hw) (rankCriticalSequenceEmbedding hl j k) (powerGraphs (Fin.last k))).mpr
    rw [rootGraph, rankClassImage_embeddingGraph hl, outputGraph]

def rankRootOutputIndex (k : Nat) : Fin (1 + (k + 3)) := ⟨0, by omega⟩
def rankRootBaseIndex (k : Nat) : Fin (1 + (k + 3)) := ⟨1, by omega⟩
def rankRootTruthIndex (k : Nat) : Fin (1 + (k + 3)) := ⟨2, by omega⟩
def rankRootPowerIndex (k : Nat) (i : Fin (k + 1)) : Fin (1 + (k + 3)) := ⟨i.val + 3, by omega⟩

def rankRootMatrix (k : Nat) : RankPredicateFormula (1 + (k + 3)) 6 :=
  rankRootTermMatrix k (rankRootBaseIndex k) (rankRootTruthIndex k) (rankRootOutputIndex k) (rankRootPowerIndex k)

theorem rankRootMatrix_output {lambda : Ordinal.{u}} (k : Nat) (graph : RankClass lambda)
    (witnesses : Fin (k + 3) → RankClass lambda) :
    Fin.append (fun _ : Fin 1 => graph) witnesses (rankRootOutputIndex k) = graph :=
  Fin.append_left (fun _ : Fin 1 => graph) witnesses 0

noncomputable def rankRootMatrixWitnesses {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : Nat) (j : RankElementaryEmbedding lambda) : Fin (k + 3) → RankClass lambda :=
  Fin.cons (rankEmbeddingClassGraph j)
    (Fin.cons (rankSatisfaction hl) (fun i : Fin (k + 1) => rankEmbeddingClassGraph (rankCriticalSequenceEmbedding hl j i.val)))

theorem rankRootMatrix_base {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : Nat) (j : RankElementaryEmbedding lambda) (graph : RankClass lambda) :
    Fin.append (fun _ : Fin 1 => graph) (rankRootMatrixWitnesses hl k j) (rankRootBaseIndex k) =
      rankEmbeddingClassGraph j := by
  change Fin.append (fun _ : Fin 1 => graph) (rankRootMatrixWitnesses hl k j) (Fin.natAdd 1 0) = _
  rw [Fin.append_right]
  rfl

theorem rankRootMatrix_truth {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : Nat) (j : RankElementaryEmbedding lambda) (graph : RankClass lambda) :
    Fin.append (fun _ : Fin 1 => graph) (rankRootMatrixWitnesses hl k j) (rankRootTruthIndex k) =
      rankSatisfaction hl := by
  change Fin.append (fun _ : Fin 1 => graph) (rankRootMatrixWitnesses hl k j) (Fin.natAdd 1 1) = _
  rw [Fin.append_right]
  rfl

theorem rankRootMatrix_power {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : Nat) (j : RankElementaryEmbedding lambda) (graph : RankClass lambda) (i : Fin (k + 1)) :
    Fin.append (fun _ : Fin 1 => graph) (rankRootMatrixWitnesses hl k j) (rankRootPowerIndex k i) =
      rankEmbeddingClassGraph (rankCriticalSequenceEmbedding hl j i.val) := by
  have index : rankRootPowerIndex k i = Fin.natAdd 1 i.succ.succ := Fin.ext (by simp [rankRootPowerIndex]; omega)
  rw [index, Fin.append_right]
  change Fin.cons _ (Fin.cons _ _) i.succ.succ = _
  rw [Fin.cons_succ, Fin.cons_succ]

/-- The entire elementary-root predicate, including actual critical point
and exact finite application equation, has a genuine finite Sigma-one
definition. No root-extraction property is postulated. -/
theorem rankRootExists_sigmaOne {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (k : Nat) (graph : RankClass lambda) :
    rankSigmaOneSatisfies (p := k + 3) (rankRootMatrix k) (fun _ : Fin 1 => graph) (rankSyntaxBooks hw) ↔
      RankRootExists hl k graph := by
  constructor
  · rintro ⟨witnesses, matrix⟩
    have result := rankRootTermMatrix_sound hl hw k _ _ _ _ _ matrix
    rwa [rankRootMatrix_output] at result
  · rintro ⟨j, critical, cp, outputEq⟩
    refine ⟨rankRootMatrixWitnesses hl k j, ?_⟩
    apply rankRootTermMatrix_complete hl hw k _ _ _ _ _ j cp
    · exact rankRootMatrix_base hl k j graph
    · exact rankRootMatrix_truth hl k j graph
    · exact rankRootMatrix_power hl k j graph
    · rw [rankRootMatrix_output]
      exact outputEq.symm

theorem rankRootExists_lowRankDefinable {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (k : Nat) : RankSigmaOneClassLowRankDefinable (RankRootExists hl k) := by
  exact ⟨6, rankSyntaxBooks hw, rankSyntaxBooks_rank_le hw, k + 3, rankRootMatrix k,
    rankRootExists_sigmaOne hl hw k⟩

end FullMarkedBLP
