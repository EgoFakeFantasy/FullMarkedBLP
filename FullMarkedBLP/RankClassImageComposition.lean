import FullMarkedBLP.RankClassImage

namespace FullMarkedBLP

/-- Image restrictions agree as actual sets, not merely on pointwise images. -/
theorem rankClassRestriction_image {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (a : RankClass lambda) (domain : RankDomain lambda) :
    rankClassRestriction (rankClassImage j a) (j domain) = j (rankClassRestriction a domain) := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    let x := rankMember (rankClassRestriction (rankClassImage j a) (j domain)) z member
    have parts := (rankClassRestriction_mem (rankClassImage j a) (j domain) x).mp member
    exact (rankClassImage_on_domain j a domain x parts.1).mp parts.2
  · intro member
    let x := rankMember (j (rankClassRestriction a domain)) z member
    have inside := (rankElementary_subset_iff j _ _).mpr (rankClassRestriction_subset a domain) member
    exact (rankClassRestriction_mem (rankClassImage j a) (j domain) x).mpr
      ⟨inside, (rankClassImage_on_domain j a domain x inside).mpr member⟩

theorem rankClassImage_iff_imageDomains {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (a : RankClass lambda) (k : RankElementaryEmbedding lambda)
    (x : RankDomain lambda) :
    rankClassImage j a x ↔ ∃ domain : RankDomain lambda,
      x.val ∈ (j (rankClassRestriction a (k domain))).val := by
  constructor
  · rintro ⟨original, member⟩
    let level := rankHierarchy (⟨original.val.rank, original.property⟩ : OrdinalDomain lambda)
    have included : original.val ⊆ (k level).val := fun _ hz =>
      rankHierarchy_subset_image hl k _ (ZFSet.subset_vonNeumann_self original.val hz)
    exact ⟨level, (rankElementary_subset_iff j _ _).mpr
      (rankClassRestriction_mono (fun _ h => h) included) member⟩
  · rintro ⟨domain, member⟩
    exact ⟨k domain, member⟩

/-- The semiconjugacy law holds for every class, including entire embedding graphs. -/
theorem rankClassImage_semiconjugacy {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (a : RankClass lambda) :
    rankClassImage j (rankClassImage k a) = rankClassImage (rankApply hl j k) (rankClassImage j a) := by
  funext x
  apply propext
  rw [rankClassImage_iff_imageDomains hl j (rankClassImage k a) k,
    rankClassImage_iff_imageDomains hl (rankApply hl j k) (rankClassImage j a) j]
  apply exists_congr
  intro domain
  rw [rankClassRestriction_image, rankClassRestriction_image, rankApply_on_image hl]

theorem rankEmbeddingClassGraph_pair {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (x y : RankDomain lambda) :
    rankEmbeddingClassGraph k (rankOrderedPair hl x y) ↔ k x = y := by
  constructor
  · rintro ⟨a, b, pair, image⟩
    have same := ZFSet.pair_inj.mp pair
    have ax : a = x := Subtype.ext same.1.symm
    have by' : b = y := Subtype.ext same.2.symm
    rwa [ax, by'] at image
  · exact fun image => ⟨x, y, rfl, image⟩

theorem rankEmbeddingClassGraph_injective {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) :
    Function.Injective (@rankEmbeddingClassGraph lambda) := by
  intro j k same
  apply FirstOrder.Language.ElementaryEmbedding.ext
  intro x
  have member := (rankEmbeddingClassGraph_pair hl j x (j x)).mpr rfl
  rw [same] at member
  exact ((rankEmbeddingClassGraph_pair hl k x (j x)).mp member).symm

/-- Left distributivity of the actual application operation. -/
theorem rankApply_left_distrib {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k l : RankElementaryEmbedding lambda) :
    rankApply hl j (rankApply hl k l) = rankApply hl (rankApply hl j k) (rankApply hl j l) := by
  apply rankEmbeddingClassGraph_injective hl
  have equation := rankClassImage_semiconjugacy hl j k (rankEmbeddingClassGraph l)
  simpa only [rankClassImage_embeddingGraph hl] using equation

end FullMarkedBLP
