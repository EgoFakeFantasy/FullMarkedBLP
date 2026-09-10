import FullMarkedBLP.RankCriticalCardinal
import FullMarkedBLP.RankCriticalLimit

namespace FullMarkedBLP

/-- A pointwise fixed set which is itself fixed has cardinality strictly below
the critical cardinal. The graph of a putative surjection is constructed in
the same rank domain. -/
theorem rankCriticalPoint_fixed_card_lt {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    {domain : RankDomain lambda} (fixedDomain : j domain = domain)
    (fixedMembers : ∀ x : RankDomain lambda, x.val ∈ domain.val → j x = x) :
    domain.val.card < critical.val.card := by
  classical
  by_contra failure
  have cardLe : critical.val.card ≤ domain.val.card := le_of_not_gt failure
  let target := ordinalDomainElement critical
  have targetCard : target.val.card = critical.val.card := Ordinal.card_toZFSet _
  have lifted : Cardinal.mk target.val ≤ Cardinal.mk domain.val := by
    rw [ZFSet.cardinalMk_coe_sort, ZFSet.cardinalMk_coe_sort, targetCard]
    exact Cardinal.lift_le.mpr cardLe
  obtain ⟨injection⟩ := (Cardinal.le_def _ _).mp lifted
  letI : Nonempty target.val := ⟨⟨Ordinal.toZFSet 0,
    Ordinal.toZFSet_mem_toZFSet_iff.mpr (rankCriticalPoint_isSuccLimit hl cp).pos⟩⟩
  let function := Function.invFun injection
  have onto : Function.Surjective function := Function.invFun_surjective injection.injective
  let graph : RankDomain lambda := ⟨zfFunctionGraph function,
    rank_function_lt_of_limit hl domain.property target.property (zfFunctionGraph_isFunc function)⟩
  exact rankCriticalPoint_no_surjection_from_fixed hl cp fixedDomain fixedMembers
    ((rankIsFunction_iff hl graph domain target).mpr (zfFunctionGraph_isFunc function))
    ((rankGraphOnto_iff hl graph domain target).mpr (zfFunctionGraph_onto function onto))

/-- Every set of rank below the critical point is smaller than the critical
cardinal, without an inaccessible-cardinal hypothesis. -/
theorem rankCriticalPoint_low_rank_card_lt {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    {domain : RankDomain lambda} (below : domain.val.rank < critical.val) :
    domain.val.card < critical.val.card := by
  apply rankCriticalPoint_fixed_card_lt hl cp (rankCriticalPoint_fixes_rank hl cp below)
  intro x hx
  exact rankCriticalPoint_fixes_rank hl cp ((ZFSet.rank_lt_of_mem hx).trans below)

/-- The critical cardinal of an actual elementary rank embedding is strong
limit. This follows by applying the low-rank size bound to powersets of
smaller initial ordinals. -/
theorem rankCriticalPoint_isStrongLimit {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    Cardinal.IsStrongLimit critical.val.card := by
  obtain ⟨c, hc⟩ := rankCriticalPoint_isCardinal hl cp
  have cardEq : critical.val.card = c := by rw [← hc, Cardinal.card_ord]
  rw [cardEq]
  refine ⟨?_, ?_⟩
  · intro zero
    have criticalZero : critical.val = 0 := by rw [← hc, zero, Cardinal.ord_zero]
    exact (rankCriticalPoint_isSuccLimit hl cp).ne_zero criticalZero
  · intro d smaller
    have ordinalBelow : d.ord < critical.val := by
      rw [← hc]
      exact Cardinal.ord_lt_ord.mpr smaller
    have powerRank : (ZFSet.powerset d.ord.toZFSet).rank < critical.val := by
      rw [ZFSet.rank_powerset, Ordinal.rank_toZFSet]
      exact (rankCriticalPoint_isSuccLimit hl cp).succ_lt ordinalBelow
    let power : RankDomain lambda := ⟨ZFSet.powerset d.ord.toZFSet,
      powerRank.trans critical.property⟩
    have small := rankCriticalPoint_low_rank_card_lt hl cp (domain := power) powerRank
    simpa only [power, ZFSet.card_powerset, Ordinal.card_toZFSet,
      Cardinal.card_ord, cardEq] using small

end FullMarkedBLP
