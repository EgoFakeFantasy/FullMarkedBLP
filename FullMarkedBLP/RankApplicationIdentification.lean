import FullMarkedBLP.RankApplication

namespace FullMarkedBLP

/-- The actual set graph of k cut off by V_alpha, as in the standard
definition of application. No definability of the external map k is needed
to separate its graph inside this bounding set. -/
noncomputable def rankTruncatedGraph {lambda : Ordinal.{u}} (k : RankElementaryEmbedding lambda)
    (alpha : OrdinalDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.sep (fun p => ∃ x y : RankDomain lambda, p = ZFSet.pair x.val y.val ∧ k x = y)
      (ZFSet.vonNeumann alpha.val), by
    have bound := ZFSet.rank_mono (show
      ZFSet.sep (fun p => ∃ x y : RankDomain lambda, p = ZFSet.pair x.val y.val ∧ k x = y)
        (ZFSet.vonNeumann alpha.val) ⊆ ZFSet.vonNeumann alpha.val from
      fun _ hp => (ZFSet.mem_sep.mp hp).1)
    rw [ZFSet.rank_vonNeumann] at bound
    exact bound.trans_lt alpha.property⟩

theorem rankTruncatedGraph_subset_restriction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    (rankTruncatedGraph k alpha).val ⊆ (rankRestrictionGraph hl k (rankHierarchy alpha)).val := by
  intro p hp
  dsimp only [rankTruncatedGraph] at hp
  obtain ⟨inside, x, y, eq, image⟩ := ZFSet.mem_sep.mp hp
  subst p
  have pairRank := ZFSet.mem_vonNeumann.mp inside
  have xSingleton : x.val ∈ ({x.val} : ZFSet) := ZFSet.mem_singleton.mpr rfl
  have singletonPair : ({x.val} : ZFSet) ∈ ZFSet.pair x.val y.val := ZFSet.mem_pair.mpr (Or.inl rfl)
  have rankBound := (ZFSet.rank_lt_of_mem xSingleton).trans (ZFSet.rank_lt_of_mem singletonPair)
  have member : x.val ∈ (rankHierarchy alpha).val := ZFSet.mem_vonNeumann.mpr (rankBound.trans pairRank)
  exact (rankGraphApplies_iff hl _ _ _).mp
    ((rankRestrictionGraph_applies_iff hl k _ x y).mpr ⟨member, image⟩)

theorem rankRestrictionGraph_subset_truncation {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (domain : RankDomain lambda) :
    (rankRestrictionGraph hl k domain).val ⊆
      (rankTruncatedGraph k ⟨(rankRestrictionGraph hl k domain).val.rank, (rankRestrictionGraph hl k domain).property⟩).val := by
  intro p hp
  dsimp only [rankTruncatedGraph]
  apply ZFSet.mem_sep.mpr
  refine ⟨ZFSet.subset_vonNeumann_self _ hp, ?_⟩
  obtain ⟨x, eq⟩ := ZFSet.mem_range.mp hp
  exact ⟨rankMember domain x.val x.property, k (rankMember domain x.val x.property), eq.symm, rfl⟩

/-- The constructed union of image restrictions is exactly the union of
j(k intersect V_alpha), not a different extension with the same image law. -/
theorem rankApplicationRel_iff_truncation {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (x y : RankDomain lambda) :
    RankApplicationRel hl j k x y ↔
      ∃ alpha : OrdinalDomain lambda, rankGraphApplies (j (rankTruncatedGraph k alpha)) x y := by
  constructor
  · rintro ⟨domain, applies⟩
    let alpha : OrdinalDomain lambda :=
      ⟨(rankRestrictionGraph hl k domain).val.rank, (rankRestrictionGraph hl k domain).property⟩
    refine ⟨alpha, (rankGraphApplies_iff hl _ _ _).mpr ?_⟩
    exact (rankElementary_subset_iff j _ _).mpr (rankRestrictionGraph_subset_truncation hl k domain)
      ((rankGraphApplies_iff hl _ _ _).mp applies)
  · rintro ⟨alpha, applies⟩
    refine ⟨rankHierarchy alpha, (rankGraphApplies_iff hl _ _ _).mpr ?_⟩
    exact (rankElementary_subset_iff j _ _).mpr (rankTruncatedGraph_subset_restriction hl k alpha)
      ((rankGraphApplies_iff hl _ _ _).mp applies)

theorem rankApply_graph_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (x y : RankDomain lambda) :
    rankApply hl j k x = y ↔
      ∃ alpha : OrdinalDomain lambda, rankGraphApplies (j (rankTruncatedGraph k alpha)) x y := by
  rw [← rankApplicationRel_iff_truncation hl j k x y]
  constructor
  · intro eq
    rw [← eq]
    exact rankApply_spec hl j k x
  · intro applies
    exact rankApplicationRel_functional hl j k (rankApply_spec hl j k x) applies

end FullMarkedBLP
