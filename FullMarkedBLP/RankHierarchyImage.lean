import FullMarkedBLP.RankHierarchyRecursion

namespace FullMarkedBLP

/-- Exact hierarchy-image identification from the transferred recursion graph. -/
theorem rankElementary_hierarchy {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    j (rankHierarchy alpha) = rankHierarchy (rankOrdinalAction j alpha) := by
  let upper : OrdinalDomain lambda := ⟨Order.succ alpha.val, hl.succ_lt alpha.property⟩
  have below : alpha < upper := Order.lt_succ alpha.val
  have function := (rankElementary_function_iff j _ _ _).mpr (rankHierarchyGraph_isFunction hl upper)
  have ordinal := (rankElementary_isOrdinal_iff j (ordinalDomainElement upper)).mpr
    (ZFSet.isOrdinal_toZFSet upper.val)
  have recursion := (rankElementary_hierarchyRec_iff j _).mpr (rankHierarchyGraph_recursion hl upper)
  have oldEdge := (rankGraphApplies_iff hl _ _ _).mp (rankHierarchyGraph_at hl below)
  have edge : rankGraphApplies (j (rankHierarchyGraph hl upper))
      (j (ordinalDomainElement alpha)) (j (rankHierarchy alpha)) :=
    (rankGraphApplies_iff hl _ _ _).mpr ((rankElementary_graph_membership_iff hl j _ _ _).mpr oldEdge)
  have member : (j (ordinalDomainElement alpha)).val ∈ (j (ordinalDomainElement upper)).val :=
    (rankElementary_mem_iff j _ _).mpr (Ordinal.toZFSet_mem_toZFSet_iff.mpr below)
  rw [← ordinalDomainElement_action j alpha] at edge member
  exact rankHierarchyRec_unique function ordinal recursion (rankOrdinalAction j alpha) _ member edge

theorem rankElementary_rank {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) :
    (j x).val.rank = (rankOrdinalAction j ⟨x.val.rank, x.property⟩).val := by
  let alpha : OrdinalDomain lambda := ⟨x.val.rank, x.property⟩
  have included := (rankElementary_subset_iff j x (rankHierarchy alpha)).mpr (ZFSet.subset_vonNeumann_self x.val)
  rw [rankElementary_hierarchy hl j alpha] at included
  apply le_antisymm (ZFSet.subset_vonNeumann.mp included)
  apply le_of_not_gt
  intro lower
  have inside : (j x).val ∈ (j (rankHierarchy alpha)).val := by
    rw [rankElementary_hierarchy hl j alpha]
    exact ZFSet.mem_vonNeumann.mpr lower
  have old := (rankElementary_mem_iff j x (rankHierarchy alpha)).mp inside
  exact (lt_irrefl x.val.rank) (ZFSet.mem_vonNeumann.mp old)

theorem rankElementary_rank_lt_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) (alpha : OrdinalDomain lambda) :
    (j x).val.rank < (rankOrdinalAction j alpha).val ↔ x.val.rank < alpha.val := by
  rw [rankElementary_rank hl j x]
  exact rankOrdinalAction_lt_iff j ⟨x.val.rank, x.property⟩ alpha

end FullMarkedBLP
