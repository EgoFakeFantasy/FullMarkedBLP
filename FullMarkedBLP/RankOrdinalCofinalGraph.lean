import FullMarkedBLP.FunctionGraphConstruction
import FullMarkedBLP.RankCofinalFormula

namespace FullMarkedBLP

/-- Translate a function between ordinal intervals into a function between
the corresponding von Neumann sets, using the rank of each ordinal member. -/
noncomputable def zfOrdinalFunction {alpha beta : Ordinal.{u}}
    (f : Set.Iio alpha → Set.Iio beta) : alpha.toZFSet → beta.toZFSet :=
  fun a => ⟨(f ⟨a.val.rank, by
    simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem a.property⟩).val.toZFSet,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr (f _).property⟩

theorem zfOrdinalFunction_apply {alpha beta : Ordinal.{u}}
    (f : Set.Iio alpha → Set.Iio beta) (a : Set.Iio alpha) :
    (zfOrdinalFunction f ⟨a.val.toZFSet,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr a.property⟩).val = (f a).val.toZFSet := by
  simp only [zfOrdinalFunction, Ordinal.rank_toZFSet]

/-- The actual set graph of an ordinal function in the original rank domain. -/
noncomputable def rankOrdinalFunctionGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (alpha beta : OrdinalDomain lambda) (f : Set.Iio alpha.val → Set.Iio beta.val) :
    RankDomain lambda :=
  ⟨zfFunctionGraph (zfOrdinalFunction f),
    rank_function_lt_of_limit hl (ordinalDomainElement alpha).property
      (ordinalDomainElement beta).property (zfFunctionGraph_isFunc (zfOrdinalFunction f))⟩

theorem rankOrdinalFunctionGraph_isFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (alpha beta : OrdinalDomain lambda) (f : Set.Iio alpha.val → Set.Iio beta.val) :
    rankIsFunction (rankOrdinalFunctionGraph hl alpha beta f)
      (ordinalDomainElement alpha) (ordinalDomainElement beta) :=
  (rankIsFunction_iff hl _ _ _).mpr (zfFunctionGraph_isFunc (zfOrdinalFunction f))

theorem rankOrdinalFunctionGraph_applies {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (alpha beta : OrdinalDomain lambda) (f : Set.Iio alpha.val → Set.Iio beta.val)
    (a : Set.Iio alpha.val) :
    rankGraphApplies (rankOrdinalFunctionGraph hl alpha beta f)
      (ordinalDomainElement ⟨a.val, a.property.trans alpha.property⟩)
      (ordinalDomainElement ⟨(f a).val, (f a).property.trans beta.property⟩) := by
  apply (rankGraphApplies_iff hl _ _ _).mpr
  exact (mem_zfFunctionGraph (zfOrdinalFunction f) _ _).mpr
    ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr a.property, zfOrdinalFunction_apply f a⟩

theorem rankOrdinalFunctionGraph_cofinal {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (alpha beta : OrdinalDomain lambda) (f : Set.Iio alpha.val → Set.Iio beta.val)
    (cofinal : ∀ b < beta.val, ∃ a, b < (f a).val) :
    rankGraphCofinal (rankOrdinalFunctionGraph hl alpha beta f)
      (ordinalDomainElement alpha) (ordinalDomainElement beta) := by
  intro b hb
  obtain ⟨bOrdinal, below, eqB⟩ := Ordinal.mem_toZFSet_iff.mp hb
  obtain ⟨a, above⟩ := cofinal bOrdinal below
  let input := ordinalDomainElement (⟨a.val, a.property.trans alpha.property⟩ : OrdinalDomain lambda)
  let output := ordinalDomainElement (⟨(f a).val, (f a).property.trans beta.property⟩ : OrdinalDomain lambda)
  refine ⟨input, Ordinal.toZFSet_mem_toZFSet_iff.mpr a.property,
    output, Ordinal.toZFSet_mem_toZFSet_iff.mpr (f a).property, ?_, ?_⟩
  · exact rankOrdinalFunctionGraph_applies hl alpha beta f a
  · change b.val ∈ (f a).val.toZFSet
    rw [← eqB]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr above

/-- A genuinely cofinal ordinal function has a graph in the same limit rank
domain, and its cofinality is expressed by the first-order graph predicate. -/
theorem rankCofinalGraph_exists {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (alpha beta : OrdinalDomain lambda) (f : Set.Iio alpha.val → Set.Iio beta.val)
    (cofinal : ∀ b < beta.val, ∃ a, b < (f a).val) :
    ∃ graph : RankDomain lambda,
      rankIsFunction graph (ordinalDomainElement alpha) (ordinalDomainElement beta) ∧
      rankGraphCofinal graph (ordinalDomainElement alpha) (ordinalDomainElement beta) :=
  ⟨rankOrdinalFunctionGraph hl alpha beta f, rankOrdinalFunctionGraph_isFunction hl alpha beta f,
    rankOrdinalFunctionGraph_cofinal hl alpha beta f cofinal⟩

end FullMarkedBLP
