import FullMarkedBLP.RankApplicationIdentification
import FullMarkedBLP.RankIntersectionPreservation

namespace FullMarkedBLP

abbrev RankClass (lambda : Ordinal.{u}) := Set (RankDomain lambda)

/-- Restrict an arbitrary external class to an actual set in the rank domain. -/
noncomputable def rankClassRestriction {lambda : Ordinal.{u}} (a : RankClass lambda)
    (domain : RankDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.sep (fun z => ∃ x : RankDomain lambda, x.val = z ∧ a x) domain.val,
    (ZFSet.rank_mono (fun _ h => (ZFSet.mem_sep.mp h).1)).trans_lt domain.property⟩

theorem rankClassRestriction_mem {lambda : Ordinal.{u}} (a : RankClass lambda)
    (domain x : RankDomain lambda) :
    x.val ∈ (rankClassRestriction a domain).val ↔ x.val ∈ domain.val ∧ a x := by
  dsimp only [rankClassRestriction]
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨member, y, same, hy⟩
    have same' : y = x := Subtype.ext same
    exact ⟨member, same' ▸ hy⟩
  · rintro ⟨member, hx⟩
    exact ⟨member, x, rfl, hx⟩

theorem rankClassRestriction_subset {lambda : Ordinal.{u}} (a : RankClass lambda)
    (domain : RankDomain lambda) : (rankClassRestriction a domain).val ⊆ domain.val := by
  intro x hx
  dsimp only [rankClassRestriction] at hx
  exact (ZFSet.mem_sep.mp hx).1

theorem rankClassRestriction_mono {lambda : Ordinal.{u}} {a b : RankClass lambda}
    {x y : RankDomain lambda} (classes : a ⊆ b) (domains : x.val ⊆ y.val) :
    (rankClassRestriction a x).val ⊆ (rankClassRestriction b y).val := by
  intro z hz
  let z' := rankMember (rankClassRestriction a x) z hz
  have member := (rankClassRestriction_mem a x z').mp hz
  exact (rankClassRestriction_mem b y z').mpr ⟨domains member.1, classes member.2⟩

/-- The standard j-plus extension, initially expressed using all bounded sets. -/
def rankClassImage {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (a : RankClass lambda) : RankClass lambda :=
  fun x => ∃ domain : RankDomain lambda, x.val ∈ (j (rankClassRestriction a domain)).val

/-- Bounded sets and hierarchy cutoffs give exactly the same extension. -/
theorem rankClassImage_iff_hierarchy {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (a : RankClass lambda) (x : RankDomain lambda) :
    rankClassImage j a x ↔ ∃ alpha : OrdinalDomain lambda,
      x.val ∈ (j (rankClassRestriction a (rankHierarchy alpha))).val := by
  constructor
  · rintro ⟨domain, member⟩
    let alpha : OrdinalDomain lambda := ⟨domain.val.rank, domain.property⟩
    refine ⟨alpha, (rankElementary_subset_iff j _ _).mpr ?_ member⟩
    exact rankClassRestriction_mono (fun _ h => h) (ZFSet.subset_vonNeumann_self domain.val)
  · rintro ⟨alpha, member⟩
    exact ⟨rankHierarchy alpha, member⟩

theorem rankClassImage_mono {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    {a b : RankClass lambda} (included : a ⊆ b) : rankClassImage j a ⊆ rankClassImage j b := by
  rintro x ⟨domain, member⟩
  exact ⟨domain, (rankElementary_subset_iff j _ _).mpr
    (rankClassRestriction_mono included (fun _ h => h)) member⟩

/-- The extension has the exact expected restriction on every image set. -/
theorem rankClassImage_on_domain {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (a : RankClass lambda) (domain x : RankDomain lambda) (inside : x.val ∈ (j domain).val) :
    rankClassImage j a x ↔ x.val ∈ (j (rankClassRestriction a domain)).val := by
  constructor
  · rintro ⟨other, member⟩
    have intersection : x.val ∈ (j (rankIntersection (rankClassRestriction a other) domain)).val := by
      rw [rankElementary_intersection]
      exact ZFSet.mem_inter.mpr ⟨member, inside⟩
    apply (rankElementary_subset_iff j _ _).mpr _ intersection
    intro z hz
    let z' := rankMember (rankIntersection (rankClassRestriction a other) domain) z hz
    have parts := ZFSet.mem_inter.mp hz
    exact (rankClassRestriction_mem a domain z').mpr
      ⟨parts.2, ((rankClassRestriction_mem a other z').mp parts.1).2⟩
  · exact fun member => ⟨domain, member⟩

theorem rankClassImage_on_image {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (a : RankClass lambda) (x : RankDomain lambda) :
    rankClassImage j a (j x) ↔ a x := by
  constructor
  · rintro ⟨domain, member⟩
    exact ((rankClassRestriction_mem a domain x).mp ((rankElementary_mem_iff j _ _).mp member)).2
  · intro hx
    let domain := rankHierarchy (⟨Order.succ x.val.rank, hl.succ_lt x.property⟩ : OrdinalDomain lambda)
    exact ⟨domain, (rankElementary_mem_iff j _ _).mpr
      ((rankClassRestriction_mem a domain x).mpr ⟨ZFSet.mem_vonNeumann_succ x.val, hx⟩)⟩

theorem rankClassImage_injective {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) : Function.Injective (rankClassImage j) := by
  intro a b same
  funext x
  apply propext
  rw [← rankClassImage_on_image hl j a x, ← rankClassImage_on_image hl j b x, same]

def rankEmbeddingClassGraph {lambda : Ordinal.{u}} (k : RankElementaryEmbedding lambda) : RankClass lambda :=
  fun p => ∃ x y : RankDomain lambda, p.val = ZFSet.pair x.val y.val ∧ k x = y

theorem rankClassRestriction_graph {lambda : Ordinal.{u}} (k : RankElementaryEmbedding lambda)
    (alpha : OrdinalDomain lambda) :
    rankClassRestriction (rankEmbeddingClassGraph k) (rankHierarchy alpha) = rankTruncatedGraph k alpha := by
  apply Subtype.ext
  apply ZFSet.ext
  intro p
  dsimp only [rankClassRestriction, rankEmbeddingClassGraph, rankHierarchy, rankTruncatedGraph]
  simp only [ZFSet.mem_sep]
  constructor
  · rintro ⟨member, z, same, x, y, pair, image⟩
    exact ⟨member, x, y, same.symm.trans pair, image⟩
  · rintro ⟨member, x, y, pair, image⟩
    exact ⟨member, ⟨p, (ZFSet.mem_vonNeumann.mp member).trans alpha.property⟩, rfl, x, y, pair, image⟩

theorem rankClassImage_graph_pair {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (x y : RankDomain lambda) :
    rankClassImage j (rankEmbeddingClassGraph k) (rankOrderedPair hl x y) ↔ rankApply hl j k x = y := by
  rw [rankClassImage_iff_hierarchy, rankApply_graph_iff hl]
  apply exists_congr
  intro alpha
  rw [rankClassRestriction_graph, rankGraphApplies_iff hl]
  rfl

theorem rankClassImage_embeddingGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) :
    rankClassImage j (rankEmbeddingClassGraph k) = rankEmbeddingClassGraph (rankApply hl j k) := by
  funext p
  apply propext
  constructor
  · intro member
    obtain ⟨alpha, levelMember⟩ := (rankClassImage_iff_hierarchy j _ p).mp member
    rw [rankClassRestriction_graph] at levelMember
    have restricted := (rankElementary_subset_iff j _ _).mpr
      (rankTruncatedGraph_subset_restriction hl k alpha) levelMember
    obtain ⟨x, y, _, _, pair⟩ := (rankRestrictionGraph_image_function hl j k (rankHierarchy alpha)).1 p restricted
    have same : p = rankOrderedPair hl x y := Subtype.ext ((rankIsOrderedPair_iff hl _ _ _).mp pair)
    exact ⟨x, y, congrArg Subtype.val same,
      (rankClassImage_graph_pair hl j k x y).mp (same ▸ member)⟩
  · rintro ⟨x, y, pair, image⟩
    have same : p = rankOrderedPair hl x y := Subtype.ext pair
    rw [same]
    exact (rankClassImage_graph_pair hl j k x y).mpr image

end FullMarkedBLP
