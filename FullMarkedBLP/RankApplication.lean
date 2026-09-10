import FullMarkedBLP.RankImageCofinality
import FullMarkedBLP.RankGraphElementarity

namespace FullMarkedBLP

/-- Application of two genuine elementary self-embeddings of a limit rank.
The union of image restrictions is total and fully elementary by the proved
cofinality and formula-transfer lemmas. No application closure axiom is used. -/
noncomputable def rankApply {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) : RankElementaryEmbedding lambda where
  toFun := rankApplication hl j k (rankElementary_image_cofinal hl j)
  map_formula' := by
    intro n phi xs
    obtain ⟨domain, covered⟩ := rankElementary_image_covers_tuple hl j xs
    exact rankRestrictionGraph_image_preserves_formula hl j k domain phi xs
      (rankApplication hl j k (rankElementary_image_cofinal hl j) ∘ xs)
      (fun i => rankApplication_on_domain hl j k (rankElementary_image_cofinal hl j) domain (xs i) (covered i))

theorem rankApply_spec {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (x : RankDomain lambda) :
    RankApplicationRel hl j k x (rankApply hl j k x) :=
  rankApplication_spec hl j k (rankElementary_image_cofinal hl j) x

theorem rankApply_on_image {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (x : RankDomain lambda) :
    rankApply hl j k (j x) = j (k x) :=
  rankApplication_comp hl j k (rankElementary_image_cofinal hl j) x

theorem rankApply_comp {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) : (rankApply hl j k).comp j = j.comp k := by
  apply FirstOrder.Language.ElementaryEmbedding.ext
  intro x
  exact rankApply_on_image hl j k x

theorem rankApply_ordinal_image {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    rankOrdinalAction (rankApply hl j k) (rankOrdinalAction j alpha) =
      rankOrdinalAction j (rankOrdinalAction k alpha) := by
  apply Subtype.ext
  change (rankApply hl j k (ordinalDomainElement (rankOrdinalAction j alpha))).val.rank =
    (j (ordinalDomainElement (rankOrdinalAction k alpha))).val.rank
  rw [ordinalDomainElement_action, rankApply_on_image, ordinalDomainElement_action]

end FullMarkedBLP
