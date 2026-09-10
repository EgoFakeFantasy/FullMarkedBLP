import FullMarkedBLP.RankHierarchyImage
import FullMarkedBLP.RankApplicationCritical

namespace FullMarkedBLP

/-- An elementary embedding fixes every set of rank below its critical point,
proved from exact rank preservation and rank induction. -/
theorem rankCriticalPoint_fixes_rank {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda} (critical : RankCriticalPoint j c)
    {x : RankDomain lambda} (below : x.val.rank < c.val) : j x = x := by
  have all : ∀ alpha : Ordinal.{u}, ∀ z : RankDomain lambda, z.val.rank = alpha → alpha < c.val → j z = z := by
    intro alpha
    apply (wellFounded_lt : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)).induction alpha
    intro level ih z rank below
    let ordinal : OrdinalDomain lambda := ⟨z.val.rank, z.property⟩
    have fixedRank : rankOrdinalAction j ordinal = ordinal := critical.2 ordinal (by
      change z.val.rank < c.val
      rw [rank]
      exact below)
    have imageRank : (j z).val.rank = z.val.rank := (rankElementary_rank hl j z).trans (congrArg Subtype.val fixedRank)
    apply Subtype.ext
    apply ZFSet.ext
    intro w
    constructor
    · intro hw
      have smaller : w.rank < level := (ZFSet.rank_lt_of_mem hw).trans_eq (imageRank.trans rank)
      let w' := rankMember (j z) w hw
      have fixed := ih w.rank smaller w' rfl (smaller.trans below)
      have inside : (j w').val ∈ (j z).val := by rw [fixed]; exact hw
      exact (rankElementary_mem_iff j w' z).mp inside
    · intro hw
      have smaller : w.rank < level := (ZFSet.rank_lt_of_mem hw).trans_eq rank
      let w' := rankMember z w hw
      have fixed := ih w.rank smaller w' rfl (smaller.trans below)
      have inside := (rankElementary_mem_iff j w' z).mpr hw
      rw [fixed] at inside
      exact inside
  exact all x.val.rank x rfl below

/-- Below the critical point of the outer embedding, its application to k
has precisely the same weak membership restriction as k. -/
theorem rankApply_agrees_below_critical {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda} (critical : RankCriticalPoint j c)
    (k : RankElementaryEmbedding lambda) : rankCutoffAgreement c.val (rankApply hl j k) k := by
  intro x z hx hz
  have fixedX := rankCriticalPoint_fixes_rank hl critical hx
  have fixedZ := rankCriticalPoint_fixes_rank hl critical hz
  have image := rankApply_on_image hl j k z
  rw [fixedZ] at image
  rw [image]
  have membership := rankElementary_mem_iff j x (k z)
  rw [fixedX] at membership
  exact membership

end FullMarkedBLP
