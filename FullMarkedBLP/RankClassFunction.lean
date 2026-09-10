import FullMarkedBLP.RankTruthMatrixCorrectness

namespace FullMarkedBLP

def rankFunctionClassGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (f : RankDomain lambda → RankDomain lambda) : RankClass lambda :=
  fun p => ∃ x y, p = rankOrderedPair hl x y ∧ f x = y

theorem rankFunctionClassGraph_pair {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (f : RankDomain lambda → RankDomain lambda) (x y : RankDomain lambda) :
    rankTruthHolds hl (rankFunctionClassGraph hl f) x y ↔ f x = y := by
  constructor
  · rintro ⟨a, b, same, value⟩
    obtain ⟨rfl, rfl⟩ := (rankOrderedPair_inj hl _ _ _ _).mp same
    exact value
  · exact fun h => ⟨x, y, rfl, h⟩

/-- A genuine total function on the whole rank domain, encoded by a class
containing exactly ordered pairs. Elementarity is not part of this structure. -/
structure RankClassFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (graph : RankClass lambda) : Prop where
  pairs : ∀ p, graph p → ∃ x y, p = rankOrderedPair hl x y
  total : ∀ x, ∃! y, rankTruthHolds hl graph x y

noncomputable def RankClassFunction.map {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    {graph : RankClass lambda} (function : RankClassFunction hl graph) (x : RankDomain lambda) :
    RankDomain lambda := Classical.choose (function.total x)

theorem RankClassFunction.map_spec {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    {graph : RankClass lambda} (function : RankClassFunction hl graph) (x : RankDomain lambda) :
    rankTruthHolds hl graph x (function.map x) := (Classical.choose_spec (function.total x)).1

theorem RankClassFunction.map_iff {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    {graph : RankClass lambda} (function : RankClassFunction hl graph) (x y : RankDomain lambda) :
    rankTruthHolds hl graph x y ↔ function.map x = y := by
  constructor
  · exact fun h => ((Classical.choose_spec (function.total x)).2 y h).symm
  · intro h
    rw [← h]
    exact function.map_spec x

theorem rankFunctionClassGraph_function {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (f : RankDomain lambda → RankDomain lambda) : RankClassFunction hl (rankFunctionClassGraph hl f) := by
  constructor
  · rintro p ⟨x, y, same, _⟩
    exact ⟨x, y, same⟩
  · intro x
    refine ⟨f x, (rankFunctionClassGraph_pair hl f x _).mpr rfl, ?_⟩
    intro y hy
    exact ((rankFunctionClassGraph_pair hl f x y).mp hy).symm

theorem RankClassFunction.graph_map {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    {graph : RankClass lambda} (function : RankClassFunction hl graph) :
    rankFunctionClassGraph hl function.map = graph := by
  ext p
  constructor
  · rintro ⟨x, y, rfl, same⟩
    exact (function.map_iff x y).mpr same
  · intro member
    obtain ⟨x, y, rfl⟩ := function.pairs p member
    exact ⟨x, y, rfl, (function.map_iff x y).mp member⟩

theorem rankFunctionClassGraph_embedding {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) : rankFunctionClassGraph hl j = rankEmbeddingClassGraph j := by
  ext p
  constructor
  · rintro ⟨x, y, same, value⟩
    exact ⟨x, y, congrArg Subtype.val same, value⟩
  · rintro ⟨x, y, same, value⟩
    exact ⟨x, y, Subtype.ext same, value⟩

def rankClassFunctionMatrix : RankPredicateFormula 1 0 :=
  let pairBody : RankPredicateFormula 1 3 := rankFormulaOrderedPair 0 1 2
  let pairs : RankPredicateFormula 1 1 := .imp (.predicate 0 0) pairBody.ex.ex
  let uniqueBody : RankPredicateFormula 1 3 := .imp (rankFormulaTruthHolds 0 0 2) (.equal 2 1)
  let totalBody : RankPredicateFormula 1 2 := (rankFormulaTruthHolds 0 0 1).and uniqueBody.all
  pairs.all.and totalBody.ex.all

theorem rankClassFunctionMatrix_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (graph : RankClass lambda) :
    rankClassFunctionMatrix.Realize (fun _ => graph) Fin.elim0 ↔ RankClassFunction hl graph := by
  have pairs : (∀ p : RankDomain lambda, graph p → ∃ x y, rankIsOrderedPair p x y) ↔
      ∀ p : RankDomain lambda, graph p → ∃ x y, p = rankOrderedPair hl x y := by
    apply forall_congr'
    intro p
    apply imp_congr_right
    intro _
    apply exists_congr
    intro x
    apply exists_congr
    intro y
    exact (rankIsOrderedPair_iff hl _ _ _).trans
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have result : ((∀ p : RankDomain lambda, graph p → ∃ x y, rankIsOrderedPair p x y) ∧
      ∀ x, ∃! y, rankTruthHolds hl graph x y) ↔ RankClassFunction hl graph := by
    rw [pairs]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.pairs, h.total⟩⟩
  simp only [rankClassFunctionMatrix, RankPredicateFormula.realize_and,
    RankPredicateFormula.Realize, RankPredicateFormula.realize_ex,
    rankFormulaTruthHolds_realize hl, rankFormulaOrderedPair_realize]
  simpa [Fin.snoc, ExistsUnique] using result

end FullMarkedBLP
