import FullMarkedBLP.RankApplicationBelowCritical
import FullMarkedBLP.RankCardinalPreservation

namespace FullMarkedBLP

/-- A set which is fixed together with all its members cannot surject onto
the critical ordinal. The image function would have to hit the newly added
critical ordinal using an input whose old value is already fixed below it. -/
theorem rankCriticalPoint_no_surjection_from_fixed {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    {domain graph : RankDomain lambda} (fixedDomain : j domain = domain)
    (fixedMembers : ∀ x : RankDomain lambda, x.val ∈ domain.val → j x = x)
    (function : rankIsFunction graph domain (ordinalDomainElement critical))
    (onto : rankGraphOnto graph domain (ordinalDomainElement critical)) : False := by
  have imageFunction := (rankElementary_function_iff j graph domain (ordinalDomainElement critical)).mpr function
  have imageOnto := (rankElementary_onto_iff j graph domain (ordinalDomainElement critical)).mpr onto
  have moved : (ordinalDomainElement critical).val ∈ (j (ordinalDomainElement critical)).val := by
    rw [rankOrdinalAction_compat]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (rankCriticalPoint_lt_image cp)
  obtain ⟨x, hx, imageEdge⟩ := imageOnto (ordinalDomainElement critical) moved
  have oldMember : x.val ∈ domain.val := by simpa only [fixedDomain] using hx
  obtain ⟨y, hy, oldEdge, _⟩ := function.2 x oldMember
  have fixedX := fixedMembers x oldMember
  have fixedY : j y = y := rankCriticalPoint_fixes_rank hl cp (by
    have below := ZFSet.rank_lt_of_mem hy
    simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using below)
  have mappedEdge : rankGraphApplies (j graph) x y := by
    rw [← fixedX, ← fixedY, rankGraphApplies_iff hl]
    exact (rankElementary_graph_membership_iff hl j x y graph).mpr ((rankGraphApplies_iff hl _ _ _).mp oldEdge)
  obtain ⟨z, _, _, unique⟩ := imageFunction.2 x hx
  have same : ordinalDomainElement critical = y :=
    (unique _ imageEdge).trans (unique _ mappedEdge).symm
  rw [← same] at hy
  exact (lt_irrefl _) (ZFSet.rank_lt_of_mem hy)

/-- The least moved ordinal of a genuine rank embedding is an initial
ordinal. This is proved by transporting a hypothetical smaller bijection,
not assumed as part of RankCriticalPoint. -/
theorem rankCriticalPoint_isCardinal {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    ∃ c : Cardinal.{u}, c.ord = critical.val := by
  apply (ordinal_cardinal_iff_no_rank_bijection hl critical).mpr
  intro smaller below
  rintro ⟨graph, bijection⟩
  apply rankCriticalPoint_no_surjection_from_fixed hl cp
    (rankCriticalPoint_fixed_set cp below) ?_ bijection.1 bijection.2.1
  intro x hx
  apply rankCriticalPoint_fixes_rank hl cp
  have rankBound := ZFSet.rank_lt_of_mem hx
  have rankBound' : x.val.rank < smaller.val := by
    simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using rankBound
  exact rankBound'.trans below

end FullMarkedBLP
