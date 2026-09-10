import FullMarkedBLP.RankRestrictionGraph

namespace FullMarkedBLP

/-- Application as the union of images of all set-sized restrictions. Its
functionality is unconditional; totality is proved below under membership
cofinality, which RankImageCofinality derives for all limit-rank embeddings. -/
def RankApplicationRel {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (x y : RankDomain lambda) : Prop :=
  ∃ domain : RankDomain lambda, rankGraphApplies (j (rankRestrictionGraph hl k domain)) x y

theorem rankApplicationRel_functional {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) {x y z : RankDomain lambda}
    (hy : RankApplicationRel hl j k x y) (hz : RankApplicationRel hl j k x z) : y = z := by
  obtain ⟨left, hy⟩ := hy
  obtain ⟨right, hz⟩ := hz
  let domain : RankDomain lambda := ⟨left.val ∪ right.val, by
    rw [ZFSet.rank_union]
    exact max_lt left.property right.property⟩
  have leftSub : left.val ⊆ domain.val := fun _ hm => ZFSet.mem_union.mpr (Or.inl hm)
  have rightSub : right.val ⊆ domain.val := fun _ hm => ZFSet.mem_union.mpr (Or.inr hm)
  have py := rankRestrictionGraph_image_subset hl j k leftSub ((rankGraphApplies_iff hl _ _ _).mp hy)
  have pz := rankRestrictionGraph_image_subset hl j k rightSub ((rankGraphApplies_iff hl _ _ _).mp hz)
  have function := (rankIsFunction_iff hl _ _ _).mp (rankRestrictionGraph_image_function hl j k domain)
  have hx := (ZFSet.pair_mem_prod.mp (function.1 py)).1
  obtain ⟨_, _, unique⟩ := function.2 x.val hx
  exact Subtype.ext ((unique y.val py).trans (unique z.val pz).symm)

/-- A concrete coverage condition on the images of sets, not an application axiom. -/
def RankImageCofinal {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda) : Prop :=
  ∀ x : RankDomain lambda, ∃ domain : RankDomain lambda, x.val ∈ (j domain).val

theorem rankApplicationRel_total {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (cofinal : RankImageCofinal j) (x : RankDomain lambda) :
    ∃ y, RankApplicationRel hl j k x y := by
  obtain ⟨domain, hx⟩ := cofinal x
  obtain ⟨y, _, applies, _⟩ := (rankRestrictionGraph_image_function hl j k domain).2 x hx
  exact ⟨y, domain, applies⟩

noncomputable def rankApplication {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (cofinal : RankImageCofinal j) :
    RankDomain lambda → RankDomain lambda :=
  fun x => Classical.choose (rankApplicationRel_total hl j k cofinal x)

theorem rankApplication_spec {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (cofinal : RankImageCofinal j) (x : RankDomain lambda) :
    RankApplicationRel hl j k x (rankApplication hl j k cofinal x) :=
  Classical.choose_spec (rankApplicationRel_total hl j k cofinal x)

theorem rankApplication_on_domain {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (cofinal : RankImageCofinal j)
    (domain x : RankDomain lambda) (hx : x.val ∈ (j domain).val) :
    rankGraphApplies (j (rankRestrictionGraph hl k domain)) x (rankApplication hl j k cofinal x) := by
  obtain ⟨y, _, applies, _⟩ := (rankRestrictionGraph_image_function hl j k domain).2 x hx
  have eq := rankApplicationRel_functional hl j k (rankApplication_spec hl j k cofinal x) ⟨domain, applies⟩
  rw [eq]
  exact applies

theorem rankApplication_comp {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (cofinal : RankImageCofinal j) (x : RankDomain lambda) :
    rankApplication hl j k cofinal (j x) = j (k x) := by
  have inside : x.val ∈ (rankUnorderedPair hl x x).val := ZFSet.mem_pair.mpr (Or.inl rfl)
  exact rankApplicationRel_functional hl j k (rankApplication_spec hl j k cofinal (j x))
    ⟨rankUnorderedPair hl x x, rankRestrictionGraph_image_commutes hl j k _ x inside⟩

end FullMarkedBLP
