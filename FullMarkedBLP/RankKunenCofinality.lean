import FullMarkedBLP.RankCriticalJonsson
import FullMarkedBLP.RankJonssonConstruction
import FullMarkedBLP.RankFunctionPreimage
import FullMarkedBLP.RankCriticalNotImage

namespace FullMarkedBLP

/-- Kunen's omega-Jonsson contradiction: the critical supremum cannot be
strictly below the height of a limit rank domain. All colorings, function
spaces, image sets and preimage graphs are constructed in that same domain. -/
theorem rankCriticalSupremum_not_lt_domain {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    ¬rankCriticalSupremum j critical < lambda := by
  intro inside
  have omegaBelow := rankCriticalPoint_omega_lt hl cp
  have hw : Ordinal.omega0 < lambda := omegaBelow.trans critical.property
  let omega := ordinalDomainElement (⟨Ordinal.omega0, hw⟩ : OrdinalDomain lambda)
  let supremum : OrdinalDomain lambda := ⟨rankCriticalSupremum j critical, inside⟩
  let target := ordinalDomainElement supremum
  have fixedOmega : j omega = omega := by
    change j (ordinalDomainElement ⟨Ordinal.omega0, hw⟩) = _
    rw [← ordinalDomainElement_action, rankOrdinalAction_omega]
  have fixedOmegaMembers : ∀ a : RankDomain lambda, a.val ∈ omega.val → j a = a := by
    intro a ha
    apply rankCriticalPoint_fixes_rank hl cp
    have below : a.val.rank < Ordinal.omega0 := by
      simpa only [omega, ordinalDomainElement, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem ha
    exact below.trans omegaBelow
  have fixedTarget : j target = target := by
    change j (ordinalDomainElement ⟨rankCriticalSupremum j critical, inside⟩) = _
    rw [← ordinalDomainElement_action, rankCriticalSupremum_fixed_of_lt hl cp]
  obtain ⟨color, jonsson⟩ := rankCriticalSupremum_omegaJonsson hl cp
  obtain ⟨graph, function, graphJonsson⟩ := rankJonssonGraph_exists hl hw target color jonsson
  let space := rankFunctionSpace hl omega target
  have imageFunction := (rankElementary_function_iff j graph space target).mpr function
  have imageJonsson := (rankElementary_jonsson_iff j graph omega target).mpr graphJonsson
  rw [fixedOmega, fixedTarget] at imageJonsson
  let image := rankPointwiseImage j target
  have included : image.val ⊆ target.val := by
    have subset := rankPointwiseImage_subset j target
    simpa only [fixedTarget] using subset
  obtain ⟨bijection, bijective⟩ := (rankBijection_exists_iff_card_eq hl target image).mpr
    (rankPointwiseImage_card_eq j target).symm
  have criticalMember : (ordinalDomainElement critical).val ∈ target.val :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr (rankCriticalSequence_lt_supremum cp 0)
  obtain ⟨sequence, sequenceFunction, criticalEdge⟩ :=
    imageJonsson image included bijection bijective (ordinalDomainElement critical) criticalMember
  obtain ⟨oldSequence, oldFunction, imageSequence⟩ :=
    rankFunction_preimage_of_pointwiseImage hl j omega target fixedOmega fixedOmegaMembers sequenceFunction
  have oldMember : oldSequence.val ∈ space.val :=
    ZFSet.mem_funs.mpr ((rankIsFunction_iff hl _ _ _).mp oldFunction)
  obtain ⟨value, _, oldEdge, _⟩ := function.2 oldSequence oldMember
  have mappedEdge : rankGraphApplies (j graph) sequence (j value) := by
    rw [← imageSequence, rankGraphApplies_iff hl]
    exact (rankElementary_graph_membership_iff hl j oldSequence value graph).mpr
      ((rankGraphApplies_iff hl _ _ _).mp oldEdge)
  have sequenceMember : sequence.val ∈ (j space).val := by
    rw [← imageSequence]
    exact (rankElementary_mem_iff j oldSequence space).mpr oldMember
  obtain ⟨imageValue, _, _, unique⟩ := imageFunction.2 sequence sequenceMember
  have forbidden : j value = ordinalDomainElement critical :=
    (unique _ mappedEdge).trans (unique _ criticalEdge).symm
  exact rankCriticalPoint_not_image cp value forbidden

/-- Every nontrivial elementary embedding of a limit rank domain has critical
sequence cofinal in that exact domain height. This is a proved Kunen input,
not a cofinality field in the definition of the embedding. -/
theorem rankCriticalSupremum_eq_domain {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    rankCriticalSupremum j critical = lambda :=
  (rankCriticalSupremum_le_domain j critical).antisymm
    (le_of_not_gt (rankCriticalSupremum_not_lt_domain hl cp))

theorem rankCriticalSequence_cofinal {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (bound : OrdinalDomain lambda) :
    ∃ n, bound < rankCriticalSequence j critical n := by
  apply rankCriticalSupremum_cofinal j critical
  rw [rankCriticalSupremum_eq_domain hl cp]
  exact bound.property

end FullMarkedBLP
