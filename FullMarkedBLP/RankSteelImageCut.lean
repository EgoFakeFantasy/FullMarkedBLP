import FullMarkedBLP.RankSteelCollapse
import FullMarkedBLP.RankSteelEvaluationImage

namespace FullMarkedBLP

theorem rankSteelHull_ordinalImage_mem {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (beta gamma : OrdinalDomain lambda)
    (limit : Order.IsSuccLimit gamma.val) (below : beta < gamma) :
    (ordinalDomainElement (rankOrdinalAction j beta)).val ∈ (rankSteelHull hl j gamma).val := by
  let zero : OrdinalDomain lambda := ⟨0, hl.pos⟩
  let one : OrdinalDomain lambda := ⟨Order.succ 0, hl.succ_lt hl.pos⟩
  let target : OrdinalDomain lambda := ⟨Order.succ beta.val, hl.succ_lt beta.property⟩
  let constant : (ordinalDomainElement one).val → (ordinalDomainElement target).val :=
    fun _ => ⟨beta.val.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ _)⟩
  let graph := rankFunctionGraph hl (ordinalDomainElement one) (ordinalDomainElement target) constant
  have function := rankFunctionGraph_isFunction hl (ordinalDomainElement one) (ordinalDomainElement target) constant
  have graphSmall : graph.val.rank < gamma.val := by
    apply rank_function_lt_of_limit (x := (ordinalDomainElement one).val)
      (y := (ordinalDomainElement target).val) limit
    · simpa only [ordinalDomainElement, Ordinal.rank_toZFSet, one] using limit.succ_lt limit.pos
    · simpa only [ordinalDomainElement, Ordinal.rank_toZFSet, target] using limit.succ_lt below
    · exact (rankIsFunction_iff hl _ _ _).mp function
  have edge : rankGraphApplies graph (ordinalDomainElement zero) (ordinalDomainElement beta) := by
    exact (rankFunctionGraph_applies_iff hl _ _ constant _ _).mpr
      ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ _), rfl⟩
  have image := (rankElementary_graph_membership_iff hl j _ _ _).mpr
    ((rankGraphApplies_iff hl _ _ _).mp edge)
  have zeroFixed : j (ordinalDomainElement zero) = ordinalDomainElement zero := by
    rw [← ordinalDomainElement_action, rankOrdinalAction_zero hl j]
  rw [zeroFixed, ← ordinalDomainElement_action] at image
  exact (rankSteelHull_mem hl j gamma _).mpr
    ⟨graph, ordinalDomainElement zero, graphSmall,
      by simpa only [ordinalDomainElement, Ordinal.rank_toZFSet, zero] using limit.pos,
      ⟨ordinalDomainElement one, ordinalDomainElement target, function, ZFSet.isOrdinal_toZFSet _⟩, image⟩

/-- The image of the collapse sends the entire child hull below a member
of the parent hull. This is the proper-initial-segment step in Steel's proof. -/
theorem rankSteelImageCut_exists {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda)
    {owner : RankElementaryEmbedding lambda} {gamma : OrdinalDomain lambda}
    (cp : RankCriticalPoint owner gamma) (below : alpha < gamma)
    (crosses : gamma ≤ rankOrdinalAction j alpha) :
    ∃ cut h : RankDomain lambda, cut.val ∈ (rankSteelHull hl j gamma).val ∧
      RankGraphOrderEmbedding h ∧
      ∀ delta : RankDomain lambda, delta.val ∈ (rankSteelHull hl (rankApply hl j k) gamma).val →
        ∃ value : RankDomain lambda, value.val ∈ (rankSteelHull hl j gamma).val ∧
          value.val ∈ cut.val ∧ rankGraphApplies h delta value := by
  obtain ⟨beta, betaSmall, h, composition, function, ordered, composes, ordinalFunction, small⟩ :=
    rankSteelCollapse_exists hl k alpha cp below
  refine ⟨ordinalDomainElement (rankOrdinalAction j beta), j h,
    rankSteelHull_ordinalImage_mem hl j beta gamma (rankCriticalPoint_isSuccLimit hl cp) betaSmall,
    (rankElementary_graphOrderEmbedding_iff j h).mpr ordered, ?_⟩
  intro delta member
  have larger := rankSteelHull_mono hl (rankApply hl j k) crosses member
  rw [← rankElementary_steelHull hl] at larger
  have imageFunction := (rankElementary_function_iff j _ _ _).mpr function
  obtain ⟨value, valueMember, hEdge, _⟩ := imageFunction.2 delta larger
  refine ⟨value, ?_, ?_, hEdge⟩
  · obtain ⟨f, s, hf, hs, ordF, edge⟩ := (rankSteelHull_mem hl _ gamma delta.val).mp member
    let input := rankOrderedPair hl f s
    have evaluation : RankSteelEvaluates (rankApply hl j k) (rankOrdinalAction j alpha)
        input.val delta.val := ⟨f, s, hf.trans_le crosses, hs.trans_le crosses, ordF, rfl, edge⟩
    have gEdge := (rankElementary_steelEvaluation_applies_iff hl j k alpha input delta).mpr evaluation
    have compositionEdge := ((rankElementary_graphComposes_iff j _ _ _).mpr composes) input delta value gEdge hEdge
    exact (rankSteelHull_mem hl j gamma value.val).mpr
      ⟨composition, input, small, rank_orderedPair_lt_of_limit (rankCriticalPoint_isSuccLimit hl cp) hf hs,
        ordinalFunction, (rankGraphApplies_iff hl _ _ _).mp compositionEdge⟩
  · rwa [ordinalDomainElement_action]

end FullMarkedBLP
