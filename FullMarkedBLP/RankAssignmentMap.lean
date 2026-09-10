import FullMarkedBLP.RankClassFunction
import FullMarkedBLP.RankFormulaRelabel

namespace FullMarkedBLP

def rankAssignmentMapped {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (graph : RankClass lambda) (source target : RankDomain lambda) : Prop :=
  ∀ i x y, rankGraphApplies source i x → rankTruthHolds hl graph x y → rankGraphApplies target i y

theorem rankAssignmentMapped_map {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    {graph : RankClass lambda} (function : RankClassFunction hl graph) {n : Nat}
    (values : Fin n → RankDomain lambda) :
    rankAssignmentMapped hl graph (rankAssignment hl values) (rankAssignment hl (function.map ∘ values)) := by
  intro i x y source mapped
  obtain ⟨k, same, valueEq⟩ := (rankAssignment_applies_iff hl values i x).mp source
  apply (rankAssignment_applies_iff hl (function.map ∘ values) i y).mpr
  refine ⟨k, same, ?_⟩
  change function.map (values k) = y
  rw [valueEq]
  exact (function.map_iff x y).mp mapped

theorem rankAssignmentMapped_iff {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    {graph : RankClass lambda} (function : RankClassFunction hl graph) {n : Nat}
    (source target : Fin n → RankDomain lambda) :
    rankAssignmentMapped hl graph (rankAssignment hl source) (rankAssignment hl target) ↔
      target = function.map ∘ source := by
  constructor
  · intro mapped
    funext i
    exact (rankAssignment_applies_nat_iff hl target i _).mp
      (mapped _ _ _ (rankAssignment_get hl source i) (function.map_spec (source i)))
  · rintro rfl
    exact rankAssignmentMapped_map function source

def rankAssignmentMappedMatrix {m : Nat} (graph : Fin m) : RankPredicateFormula m 2 :=
  let body : RankPredicateFormula m 5 :=
    .imp (rankFormulaGraphApplies 0 2 3) (.imp (rankFormulaTruthHolds graph 3 4)
      (rankFormulaGraphApplies 1 2 4))
  body.all.all.all

theorem rankAssignmentMappedMatrix_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m : Nat} (graph : Fin m) (classes : Fin m → RankClass lambda)
    (values : Fin 2 → RankDomain lambda) :
    (rankAssignmentMappedMatrix graph).Realize classes values ↔
      rankAssignmentMapped hl (classes graph) (values 0) (values 1) := by
  simp [rankAssignmentMappedMatrix, RankPredicateFormula.Realize, rankFormulaGraphApplies_realize,
    rankFormulaTruthHolds_realize hl, rankAssignmentMapped, Fin.snoc]

def rankFormulaAssignmentMapped {m n : Nat} (graph : Fin m) (source target : Fin n) :
    RankPredicateFormula m n := (rankAssignmentMappedMatrix graph).relabelSets ![source, target]

theorem rankFormulaAssignmentMapped_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m n : Nat} (graph : Fin m) (source target : Fin n) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) :
    (rankFormulaAssignmentMapped graph source target).Realize classes values ↔
      rankAssignmentMapped hl (classes graph) (values source) (values target) := by
  rw [rankFormulaAssignmentMapped, RankPredicateFormula.realize_relabelSets,
    rankAssignmentMappedMatrix_realize hl]
  rfl

end FullMarkedBLP
