import FullMarkedBLP.RankClassImageFormula

namespace FullMarkedBLP

def rankFormulaOrdinal {m n : Nat} (x : Fin n) : RankPredicateFormula m n :=
  rankPredicateAtom rankOrdinalFormula ![x]

theorem rankFormulaOrdinal_realize {lambda : Ordinal.{u}} {m n : Nat} (x : Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaOrdinal x).Realize classes values ↔ ZFSet.IsOrdinal (values x).val := by
  rw [rankFormulaOrdinal, rankPredicateAtom_realize, rankMapSingle]
  exact rankOrdinalFormula_realize _

def rankNontrivialMatrix : RankPredicateFormula 1 0 :=
  let body : RankPredicateFormula 1 2 :=
    (rankFormulaOrdinal 0).and ((rankFormulaTruthHolds 0 0 1).and (RankPredicateFormula.equal 0 1).not)
  body.ex.ex

theorem rankNontrivialMatrix_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (graph : RankClass lambda) :
    rankNontrivialMatrix.Realize (fun _ => graph) Fin.elim0 ↔
      ∃ x y : RankDomain lambda, ZFSet.IsOrdinal x.val ∧ rankTruthHolds hl graph x y ∧ x ≠ y := by
  simp [rankNontrivialMatrix, RankPredicateFormula.Realize, RankPredicateFormula.realize_ex,
    RankPredicateFormula.realize_and, RankPredicateFormula.realize_not,
    rankFormulaOrdinal_realize, rankFormulaTruthHolds_realize hl, Fin.snoc]

theorem rankNontrivialMatrix_critical {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) :
    rankNontrivialMatrix.Realize (fun _ => rankEmbeddingClassGraph j) Fin.elim0 ↔
      ∃ critical : OrdinalDomain lambda, RankCriticalPoint j critical := by
  rw [rankNontrivialMatrix_realize hl]
  constructor
  · rintro ⟨x, y, ordinal, graph, moved⟩
    have value : j x = y := (rankEmbeddingClassGraph_pair hl j x y).mp graph
    let o : OrdinalDomain lambda := ⟨x.val.rank, x.property⟩
    have element : ordinalDomainElement o = x := Subtype.ext ordinal.toZFSet_rank_eq
    apply rankCriticalPoint_exists j
    refine ⟨o, ?_⟩
    intro fixed
    have same := congrArg ordinalDomainElement fixed
    rw [ordinalDomainElement_action, element, value] at same
    exact moved same.symm
  · rintro ⟨critical, cp⟩
    refine ⟨ordinalDomainElement critical, j (ordinalDomainElement critical),
      ZFSet.isOrdinal_toZFSet critical.val, (rankEmbeddingClassGraph_pair hl j _ _).mpr rfl, ?_⟩
    intro fixed
    apply cp.1
    apply Subtype.ext
    change (j (ordinalDomainElement critical)).val.rank = critical.val
    rw [← fixed]
    exact Ordinal.rank_toZFSet critical.val

def rankFormulaNontrivial {m n : Nat} (graph : Fin m) : RankPredicateFormula m n :=
  (rankNontrivialMatrix.relabelClasses (fun _ => graph)).relabelSets Fin.elim0

theorem rankFormulaNontrivial_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m n : Nat} (graph : Fin m) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) (j : RankElementaryEmbedding lambda)
    (graphEq : classes graph = rankEmbeddingClassGraph j) :
    (rankFormulaNontrivial (n := n) graph).Realize classes values ↔
      ∃ critical : OrdinalDomain lambda, RankCriticalPoint j critical := by
  rw [rankFormulaNontrivial, RankPredicateFormula.realize_relabelSets,
    RankPredicateFormula.realize_relabelClasses]
  have empty : values ∘ (Fin.elim0 : Fin 0 → Fin n) = Fin.elim0 := Subsingleton.elim _ _
  have mapped : classes ∘ (fun _ : Fin 1 => graph) = fun _ => rankEmbeddingClassGraph j := by
    funext i
    exact graphEq
  rw [empty, mapped]
  exact rankNontrivialMatrix_critical hl j

end FullMarkedBLP
