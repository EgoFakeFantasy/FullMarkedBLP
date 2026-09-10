import FullMarkedBLP.RankApplicationRelation
import FullMarkedBLP.RankPowersetPreservation

namespace FullMarkedBLP

noncomputable def rankHierarchy {lambda : Ordinal.{u}} (alpha : OrdinalDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.vonNeumann alpha.val, by simpa only [ZFSet.rank_vonNeumann] using alpha.property⟩

/-- Each rank level is contained in its image. The proof uses powerset
preservation and induction on the original level, not an assumption that
the embedding already covers the ambient rank domain. -/
theorem rankHierarchy_subset_image {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    (rankHierarchy alpha).val ⊆ (j (rankHierarchy alpha)).val := by
  apply (wellFounded_lt : WellFounded ((· < ·) : OrdinalDomain lambda → OrdinalDomain lambda → Prop)).induction alpha
  intro level ih x hx
  obtain ⟨beta, less, subset⟩ := ZFSet.mem_vonNeumann'.mp hx
  let lower : OrdinalDomain lambda := ⟨beta, less.trans level.property⟩
  have lowerLt : lower < level := less
  have included := ih lower lowerLt
  have imageSubset : x ⊆ (j (rankHierarchy lower)).val := fun _ hm => included (subset hm)
  have powerMember : x ∈ (rankPowerset hl (j (rankHierarchy lower))).val := ZFSet.mem_powerset.mpr imageSubset
  rw [← rankElementary_powerset hl j (rankHierarchy lower)] at powerMember
  let next : OrdinalDomain lambda := ⟨Order.succ beta, hl.succ_lt lower.property⟩
  have nextEq : rankHierarchy next = rankPowerset hl (rankHierarchy lower) :=
    Subtype.ext (ZFSet.vonNeumann_succ beta)
  rw [← nextEq] at powerMember
  have nextLe : next.val ≤ level.val := Order.succ_le_of_lt less
  have levels : (rankHierarchy next).val ⊆ (rankHierarchy level).val := ZFSet.vonNeumann_subset_of_le nextLe
  exact (rankElementary_subset_iff j _ _).mpr levels powerMember

theorem rankElementary_image_cofinal {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) : RankImageCofinal j := by
  intro x
  let level : OrdinalDomain lambda := ⟨Order.succ x.val.rank, hl.succ_lt x.property⟩
  exact ⟨rankHierarchy level, rankHierarchy_subset_image hl j level (ZFSet.mem_vonNeumann_succ x.val)⟩

/-- A single image set covers any finite parameter tuple. -/
theorem rankElementary_image_covers_tuple {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) {n : Nat} (xs : Fin n → RankDomain lambda) :
    ∃ domain : RankDomain lambda, ∀ i, (xs i).val ∈ (j domain).val := by
  induction n with
  | zero =>
    refine ⟨⟨∅, by simpa only [ZFSet.rank_empty] using hl.pos⟩, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨tail, tailMember⟩ := ih (fun i => xs i.succ)
    obtain ⟨head, headMember⟩ := rankElementary_image_cofinal hl j (xs 0)
    let domain : RankDomain lambda := ⟨head.val ∪ tail.val, by
      rw [ZFSet.rank_union]
      exact max_lt head.property tail.property⟩
    have headSub : head.val ⊆ domain.val := fun _ hm => ZFSet.mem_union.mpr (Or.inl hm)
    have tailSub : tail.val ⊆ domain.val := fun _ hm => ZFSet.mem_union.mpr (Or.inr hm)
    refine ⟨domain, ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (rankElementary_subset_iff j _ _).mpr headSub headMember
    · exact (rankElementary_subset_iff j _ _).mpr tailSub (tailMember i)

end FullMarkedBLP
