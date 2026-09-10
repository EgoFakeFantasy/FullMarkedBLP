import FullMarkedBLP.RankSteelHullFormula
import FullMarkedBLP.RankApplication

namespace FullMarkedBLP

/-- Image restrictions describe the actual applied embedding on the entire
image domain, including arguments outside the pointwise image. -/
theorem rankApply_restriction_applies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (domain x y : RankDomain lambda) :
    rankGraphApplies (j (rankRestrictionGraph hl k domain)) x y ↔
      x.val ∈ (j domain).val ∧ rankApply hl j k x = y := by
  constructor
  · intro edge
    have function := (rankIsFunction_iff hl _ _ _).mp (rankRestrictionGraph_image_function hl j k domain)
    have member := (ZFSet.pair_mem_prod.mp (function.1 ((rankGraphApplies_iff hl _ _ _).mp edge))).1
    exact ⟨member, rankApplicationRel_functional hl j k (rankApply_spec hl j k x) ⟨domain, edge⟩⟩
  · rintro ⟨member, same⟩
    have edge := rankApplication_on_domain hl j k (rankElementary_image_cofinal hl j) domain x member
    change rankGraphApplies (j (rankRestrictionGraph hl k domain)) x (rankApply hl j k x) at edge
    rwa [same] at edge

theorem rankSteelHull_describes {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    RankSteelHullDescribes (rankSteelHull hl k alpha) (rankHierarchy alpha)
      (rankRestrictionGraph hl k (rankHierarchy alpha)) :=
  rankSteelHull_describes_of_restriction hl k alpha _ (rankRestrictionGraph_applies_iff hl k _)

/-- The exact hull-image equation needed by Steel: j sends the hull for k
at alpha to the hull for j applied to k at j(alpha). -/
theorem rankElementary_steelHull {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    j (rankSteelHull hl k alpha) = rankSteelHull hl (rankApply hl j k) (rankOrdinalAction j alpha) := by
  have image := (rankElementary_hullDescribes_iff j _ _ _).mpr (rankSteelHull_describes hl k alpha)
  rw [rankElementary_hierarchy hl] at image
  have restriction : ∀ f output : RankDomain lambda,
      rankGraphApplies (j (rankRestrictionGraph hl k (rankHierarchy alpha))) f output ↔
        f.val ∈ (rankHierarchy (rankOrdinalAction j alpha)).val ∧ rankApply hl j k f = output := by
    intro f output
    have exactRestriction := rankApply_restriction_applies_iff hl j k (rankHierarchy alpha) f output
    rw [rankElementary_hierarchy hl] at exactRestriction
    exact exactRestriction
  exact rankSteelHullDescribes_unique image
    (rankSteelHull_describes_of_restriction hl (rankApply hl j k) (rankOrdinalAction j alpha) _ restriction)

end FullMarkedBLP
