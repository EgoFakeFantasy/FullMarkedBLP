import FullMarkedBLP.RankSubsetPreservation

namespace FullMarkedBLP

/-- Restriction of a genuine elementary embedding to the members of one set.
Elementarity bounds its range by the image of that set. -/
noncomputable def rankRestrictedMap {lambda : Ordinal.{u}} (k : RankElementaryEmbedding lambda)
    (domain : RankDomain lambda) : domain.val → (k domain).val :=
  fun x => ⟨(k (rankMember domain x.val x.property)).val,
    (rankElementary_mem_iff k (rankMember domain x.val x.property) domain).mpr x.property⟩

/-- The restricted graph is itself a set in the same limit rank domain. -/
noncomputable def rankRestrictionGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (domain : RankDomain lambda) : RankDomain lambda :=
  ⟨zfFunctionGraph (rankRestrictedMap k domain), rank_function_lt_of_limit hl domain.property (k domain).property
    (zfFunctionGraph_isFunc (rankRestrictedMap k domain))⟩

theorem rankRestrictionGraph_isFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (domain : RankDomain lambda) :
    rankIsFunction (rankRestrictionGraph hl k domain) domain (k domain) :=
  (rankIsFunction_iff hl _ _ _).mpr (zfFunctionGraph_isFunc (rankRestrictedMap k domain))

theorem rankRestrictionGraph_applies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (domain x y : RankDomain lambda) :
    rankGraphApplies (rankRestrictionGraph hl k domain) x y ↔ x.val ∈ domain.val ∧ k x = y := by
  rw [rankGraphApplies_iff hl]
  change ZFSet.pair x.val y.val ∈ zfFunctionGraph (rankRestrictedMap k domain) ↔ _
  rw [mem_zfFunctionGraph]
  constructor
  · rintro ⟨hx, image⟩
    exact ⟨hx, Subtype.ext image⟩
  · rintro ⟨hx, image⟩
    exact ⟨hx, congrArg Subtype.val image⟩

theorem rankRestrictionGraph_subset {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) {small large : RankDomain lambda}
    (included : small.val ⊆ large.val) :
    (rankRestrictionGraph hl k small).val ⊆ (rankRestrictionGraph hl k large).val := by
  intro p hp
  obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hp
  change ZFSet.pair x.val (rankRestrictedMap k small x).val ∈ zfFunctionGraph (rankRestrictedMap k large)
  exact (mem_zfFunctionGraph _ _ _).mpr ⟨included x.property, rfl⟩

theorem rankRestrictionGraph_image_function {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (domain : RankDomain lambda) :
    rankIsFunction (j (rankRestrictionGraph hl k domain)) (j domain) (j (k domain)) :=
  (rankElementary_function_iff j _ _ _).mpr (rankRestrictionGraph_isFunction hl k domain)

theorem rankRestrictionGraph_image_commutes {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (domain x : RankDomain lambda) (hx : x.val ∈ domain.val) :
    rankGraphApplies (j (rankRestrictionGraph hl k domain)) (j x) (j (k x)) := by
  apply (rankGraphApplies_iff hl _ _ _).mpr
  apply (rankElementary_graph_membership_iff hl j x (k x) _).mpr
  exact (rankGraphApplies_iff hl _ _ _).mp ((rankRestrictionGraph_applies_iff hl k domain x (k x)).mpr ⟨hx, rfl⟩)

theorem rankRestrictionGraph_image_subset {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) {small large : RankDomain lambda}
    (included : small.val ⊆ large.val) :
    (j (rankRestrictionGraph hl k small)).val ⊆ (j (rankRestrictionGraph hl k large)).val :=
  (rankElementary_subset_iff j _ _).mpr (rankRestrictionGraph_subset hl k included)

end FullMarkedBLP
