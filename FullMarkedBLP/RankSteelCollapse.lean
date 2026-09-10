import FullMarkedBLP.ZFOrdinalCollection
import FullMarkedBLP.RankGraphOrder

namespace FullMarkedBLP

/-- The actual order collapse H and low-rank function H composed with G.
The collapse is not assumed as a semantic certificate. -/
theorem rankSteelCollapse_exists {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda)
    {owner : RankElementaryEmbedding lambda} {gamma : OrdinalDomain lambda}
    (cp : RankCriticalPoint owner gamma) (below : alpha < gamma) :
    ∃ beta : OrdinalDomain lambda, beta < gamma ∧
      ∃ h composition : RankDomain lambda,
        rankIsFunction h (rankSteelHull hl k alpha) (ordinalDomainElement beta) ∧
        RankGraphOrderEmbedding h ∧
        RankGraphComposes h (rankSteelEvaluationGraph hl k alpha) composition ∧
        RankOrdinalFunction composition ∧ composition.val.rank < gamma.val := by
  have small := rankSteelOrderType_lt_critical hl k alpha cp below
  let beta : OrdinalDomain lambda := ⟨rankSteelOrderType hl k alpha, small.trans gamma.property⟩
  let collection := rankSteelHullCollection hl k alpha
  let target := ordinalDomainElement beta
  let h := rankFunctionGraph hl (rankSteelHull hl k alpha) target collection.collapse
  let composite := collection.collapse ∘ rankSteelEvaluationFunction hl k alpha
  let composition := rankFunctionGraph hl (rankSteelEvaluationDomain hl k alpha) target composite
  have function := rankFunctionGraph_isFunction hl (rankSteelEvaluationDomain hl k alpha) target composite
  refine ⟨beta, small, h, composition, rankFunctionGraph_isFunction hl _ _ _,
    rankFunctionGraph_orderEmbedding hl _ _ _ collection.collapse_mem_iff,
    rankFunctionGraph_composes hl _ _ _ _ _, ?_, ?_⟩
  · exact ⟨rankSteelEvaluationDomain hl k alpha, target, function, ZFSet.isOrdinal_toZFSet beta.val⟩
  · apply rank_function_lt_of_limit (x := (rankSteelEvaluationDomain hl k alpha).val)
      (y := target.val) (f := composition.val) (rankCriticalPoint_isSuccLimit hl cp)
      (rankSteelEvaluationDomain_rank_lt hl k alpha gamma (rankCriticalPoint_isSuccLimit hl cp) below)
    · simpa only [target, ordinalDomainElement, Ordinal.rank_toZFSet] using small
    · exact (rankIsFunction_iff hl _ _ _).mp function

end FullMarkedBLP
