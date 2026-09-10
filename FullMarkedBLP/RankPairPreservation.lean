import FullMarkedBLP.RankPairFormula

namespace FullMarkedBLP

theorem rankElementary_unorderedPair {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (x y : RankDomain lambda) :
    j (rankUnorderedPair hl x y) = rankUnorderedPair hl (j x) (j y) := by
  apply Subtype.ext
  exact (rankElementary_unorderedPair_iff j (rankUnorderedPair hl x y) x y).mpr rfl

theorem rankElementary_orderedPair {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (x y : RankDomain lambda) :
    j (rankOrderedPair hl x y) = rankOrderedPair hl (j x) (j y) := by
  have he : ∀ a b : RankDomain lambda, rankOrderedPair hl a b =
      rankUnorderedPair hl (rankUnorderedPair hl a a) (rankUnorderedPair hl a b) := by
    intro a b
    apply Subtype.ext
    simp [rankOrderedPair, rankUnorderedPair, ZFSet.pair]
  rw [he, rankElementary_unorderedPair, rankElementary_unorderedPair,
    rankElementary_unorderedPair, ← he]

theorem rankElementary_graph_membership_iff {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (x y f : RankDomain lambda) :
    ZFSet.pair (j x).val (j y).val ∈ (j f).val ↔ ZFSet.pair x.val y.val ∈ f.val := by
  have hh := rankElementary_mem_iff j (rankOrderedPair hl x y) f
  rw [rankElementary_orderedPair hl j x y] at hh
  exact hh

end FullMarkedBLP
