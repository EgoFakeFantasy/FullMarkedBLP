import FullMarkedBLP.RankCriticalStrongLimit
import FullMarkedBLP.RankOrdinalCofinalGraph
import Mathlib.SetTheory.Ordinal.FundamentalSequence
import Mathlib.SetTheory.Cardinal.Regular

namespace FullMarkedBLP

/-- A fixed set with fixed members cannot be the domain of a function
strictly cofinal in the critical ordinal. -/
theorem rankCriticalPoint_no_cofinal_from_fixed {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    {domain graph : RankDomain lambda} (fixedDomain : j domain = domain)
    (fixedMembers : ∀ x : RankDomain lambda, x.val ∈ domain.val → j x = x)
    (function : rankIsFunction graph domain (ordinalDomainElement critical))
    (cofinal : rankGraphCofinal graph domain (ordinalDomainElement critical)) : False := by
  have imageFunction := (rankElementary_function_iff j graph domain (ordinalDomainElement critical)).mpr function
  have imageCofinal := (rankElementary_cofinal_iff j graph domain (ordinalDomainElement critical)).mpr cofinal
  have moved : (ordinalDomainElement critical).val ∈ (j (ordinalDomainElement critical)).val := by
    rw [rankOrdinalAction_compat]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (rankCriticalPoint_lt_image cp)
  obtain ⟨x, hx, y, _, imageEdge, above⟩ := imageCofinal (ordinalDomainElement critical) moved
  have oldMember : x.val ∈ domain.val := by simpa only [fixedDomain] using hx
  obtain ⟨oldY, hy, oldEdge, _⟩ := function.2 x oldMember
  have fixedX := fixedMembers x oldMember
  have below : oldY.val.rank < critical.val := by
    simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hy
  have fixedY : j oldY = oldY := rankCriticalPoint_fixes_rank hl cp below
  have mappedEdge : rankGraphApplies (j graph) x oldY := by
    rw [← fixedX, ← fixedY, rankGraphApplies_iff hl]
    exact (rankElementary_graph_membership_iff hl j x oldY graph).mpr
      ((rankGraphApplies_iff hl _ _ _).mp oldEdge)
  obtain ⟨z, _, _, unique⟩ := imageFunction.2 x hx
  have same : y = oldY := (unique _ imageEdge).trans (unique _ mappedEdge).symm
  rw [same] at above
  have impossible : critical.val < oldY.val.rank := by
    simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem above
  exact (lt_irrefl _) (impossible.trans below)

/-- The critical cardinal is regular. A hypothetical short fundamental
sequence is encoded as a set graph and transported by the embedding. -/
theorem rankCriticalPoint_isRegular {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    Cardinal.IsRegular critical.val.card := by
  have infinite := (rankCriticalPoint_isStrongLimit hl cp).aleph0_le
  obtain ⟨c, hc⟩ := rankCriticalPoint_isCardinal hl cp
  have cardEq : critical.val.card = c := by rw [← hc, Cardinal.card_ord]
  refine ⟨infinite, ?_⟩
  rw [cardEq, hc]
  by_contra failure
  have cofinalityBelow : critical.val.cof.ord < critical.val := by
    exact (Cardinal.ord_lt_ord.mpr (lt_of_not_ge failure)).trans_eq hc
  let smaller : OrdinalDomain lambda := ⟨critical.val.cof.ord, cofinalityBelow.trans critical.property⟩
  obtain ⟨f, hf⟩ := Ordinal.exists_isFundamentalSeq (o := critical.val) rfl
  have strictCofinal : ∀ b < critical.val, ∃ a, b < (f a).val := by
    intro b hb
    have succBelow := (rankCriticalPoint_isSuccLimit hl cp).succ_lt hb
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hf.isCofinal_range ⟨Order.succ b, succBelow⟩
    exact ⟨a, (Order.lt_succ b).trans_le ha⟩
  obtain ⟨graph, function, cofinal⟩ := rankCofinalGraph_exists hl smaller critical f strictCofinal
  apply rankCriticalPoint_no_cofinal_from_fixed hl cp
    (rankCriticalPoint_fixed_set cp cofinalityBelow) ?_ function cofinal
  intro x hx
  apply rankCriticalPoint_fixes_rank hl cp
  have below : x.val.rank < smaller.val := by
    simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hx
  exact below.trans cofinalityBelow

end FullMarkedBLP
