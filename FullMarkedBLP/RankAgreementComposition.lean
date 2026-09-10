import FullMarkedBLP.RankIntersectionPreservation
import FullMarkedBLP.RankHierarchyImage

namespace FullMarkedBLP

/-- Low-rank membership tests cannot distinguish z from its restriction to
a hierarchy level above the rank of the test, after any elementary embedding. -/
theorem rankImage_membership_truncate {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (x z : RankDomain lambda) (beta : OrdinalDomain lambda)
    (below : x.val.rank < beta.val) :
    (x.val ∈ (j z).val ↔ x.val ∈ (j (rankIntersection z (rankHierarchy beta))).val) := by
  have included : x.val ∈ (j (rankHierarchy beta)).val := by
    rw [rankElementary_hierarchy hl j beta]
    exact ZFSet.mem_vonNeumann.mpr (below.trans_le (rankOrdinalAction_le_self_image j beta))
  rw [rankElementary_intersection]
  change x.val ∈ (j z).val ↔ x.val ∈ (j z).val ∩ (j (rankHierarchy beta)).val
  simp only [ZFSet.mem_inter, included, and_true]

/-- At a limit rank cutoff, the weak two-variable agreement determines all
membership tests below that cutoff, even for inputs of arbitrary rank. -/
theorem rankAgreement_all_inputs {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {left right : RankElementaryEmbedding lambda} {delta : OrdinalDomain lambda}
    (limit : Order.IsSuccLimit delta.val) (agreement : rankCutoffAgreement delta.val left right)
    (x z : RankDomain lambda) (below : x.val.rank < delta.val) :
    x.val ∈ (left z).val ↔ x.val ∈ (right z).val := by
  let beta : OrdinalDomain lambda := ⟨Order.succ x.val.rank, (limit.succ_lt below).trans delta.property⟩
  have testBelow : x.val.rank < beta.val := Order.lt_succ _
  have truncatedBound : (rankIntersection z (rankHierarchy beta)).val.rank ≤ beta.val :=
    ZFSet.subset_vonNeumann.mp (fun _ hw => (ZFSet.mem_inter.mp hw).2)
  have clipped := agreement x (rankIntersection z (rankHierarchy beta)) below
    (truncatedBound.trans_lt (limit.succ_lt below))
  exact (rankImage_membership_truncate hl left x z beta testBelow).trans
    (clipped.trans (rankImage_membership_truncate hl right x z beta testBelow).symm)

theorem rankAgreement_intersections {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {left right : RankElementaryEmbedding lambda} {delta : OrdinalDomain lambda}
    (limit : Order.IsSuccLimit delta.val) (agreement : rankCutoffAgreement delta.val left right)
    (z : RankDomain lambda) :
    rankIntersection (left z) (rankHierarchy delta) = rankIntersection (right z) (rankHierarchy delta) := by
  apply Subtype.ext
  apply ZFSet.ext
  intro x
  change x ∈ (left z).val ∩ (rankHierarchy delta).val ↔ x ∈ (right z).val ∩ (rankHierarchy delta).val
  by_cases hx : x ∈ (rankHierarchy delta).val
  · let x' := rankMember (rankHierarchy delta) x hx
    have result := rankAgreement_all_inputs hl limit agreement x' z (ZFSet.mem_vonNeumann.mp hx)
    simpa only [ZFSet.mem_inter, hx, and_true] using result
  · simp only [ZFSet.mem_inter, hx, and_false]

/-- Postcomposition transports weak agreement to the image of a limit
cutoff. The limit hypothesis is explicit and is essential to this proof. -/
theorem rankAgreement_comp_left {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (outer : RankElementaryEmbedding lambda) {left right : RankElementaryEmbedding lambda}
    {delta : OrdinalDomain lambda} (limit : Order.IsSuccLimit delta.val)
    (agreement : rankCutoffAgreement delta.val left right) :
    rankCutoffAgreement (rankOrdinalAction outer delta).val (outer.comp left) (outer.comp right) := by
  intro x z hx _
  have same := congrArg outer (rankAgreement_intersections hl limit agreement z)
  rw [rankElementary_intersection, rankElementary_intersection] at same
  have visible : x.val ∈ (outer (rankHierarchy delta)).val := by
    rw [rankElementary_hierarchy hl outer delta]
    exact ZFSet.mem_vonNeumann.mpr hx
  change x.val ∈ (outer (left z)).val ↔ x.val ∈ (outer (right z)).val
  calc
    x.val ∈ (outer (left z)).val ↔
        x.val ∈ (rankIntersection (outer (left z)) (outer (rankHierarchy delta))).val := by
      change _ ↔ x.val ∈ (outer (left z)).val ∩ (outer (rankHierarchy delta)).val
      simp only [ZFSet.mem_inter, visible, and_true]
    _ ↔ x.val ∈ (rankIntersection (outer (right z)) (outer (rankHierarchy delta))).val := by rw [same]
    _ ↔ x.val ∈ (outer (right z)).val := by
      change x.val ∈ (outer (right z)).val ∩ (outer (rankHierarchy delta)).val ↔ _
      simp only [ZFSet.mem_inter, visible, and_true]

end FullMarkedBLP
