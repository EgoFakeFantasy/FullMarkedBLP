import FullMarkedBLP.RankGraphAbsoluteness

namespace FullMarkedBLP

def rankGraphOnto {lambda : Ordinal.{u}} (f x y : RankDomain lambda) : Prop :=
  ∀ b : RankDomain lambda, b.val ∈ y.val →
    ∃ a : RankDomain lambda, a.val ∈ x.val ∧ rankGraphApplies f a b

theorem rankGraphOnto_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (f x y : RankDomain lambda) :
    rankGraphOnto f x y ↔ ∀ b ∈ y.val, ∃ a ∈ x.val, ZFSet.pair a b ∈ f.val := by
  constructor
  · intro h b hb
    obtain ⟨a, ha, hab⟩ := h (rankMember y b hb) hb
    exact ⟨a.val, ha, (rankGraphApplies_iff hl _ _ _).mp hab⟩
  · intro h b hb
    obtain ⟨a, ha, hab⟩ := h b.val hb
    exact ⟨rankMember x a ha, ha, (rankGraphApplies_iff hl _ _ _).mpr hab⟩

def rankGraphOneToOne {lambda : Ordinal.{u}} (f x : RankDomain lambda) : Prop :=
  ∀ a c b : RankDomain lambda, a.val ∈ x.val → c.val ∈ x.val →
    rankGraphApplies f a b → rankGraphApplies f c b → a = c

theorem rankGraphOneToOne_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (f x y : RankDomain lambda) (hg : rankGraphBetween f x y) :
    rankGraphOneToOne f x ↔ ∀ a ∈ x.val, ∀ c ∈ x.val, ∀ b : ZFSet.{u},
      ZFSet.pair a b ∈ f.val → ZFSet.pair c b ∈ f.val → a = c := by
  have hg' := (rankGraphBetween_iff hl f x y).mp hg
  constructor
  · intro h a ha c hc b hab hcb
    have hb := (ZFSet.pair_mem_prod.mp (hg' hab)).2
    have he := h (rankMember x a ha) (rankMember x c hc) (rankMember y b hb) ha hc
      ((rankGraphApplies_iff hl _ _ _).mpr hab) ((rankGraphApplies_iff hl _ _ _).mpr hcb)
    exact congrArg Subtype.val he
  · intro h a c b ha hc hab hcb
    exact Subtype.ext (h a.val ha c.val hc b.val
      ((rankGraphApplies_iff hl _ _ _).mp hab) ((rankGraphApplies_iff hl _ _ _).mp hcb))

end FullMarkedBLP
