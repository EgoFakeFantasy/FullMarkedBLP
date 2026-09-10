import FullMarkedBLP.RankPairPreservation

namespace FullMarkedBLP

def rankGraphBetween {lambda : Ordinal.{u}} (f x y : RankDomain lambda) : Prop :=
  ∀ p : RankDomain lambda, p.val ∈ f.val → ∃ a b : RankDomain lambda,
    a.val ∈ x.val ∧ b.val ∈ y.val ∧ rankIsOrderedPair p a b

theorem rankGraphBetween_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (f x y : RankDomain lambda) :
    rankGraphBetween f x y ↔ f.val ⊆ ZFSet.prod x.val y.val := by
  constructor
  · intro h p hp
    obtain ⟨a, b, ha, hb, he⟩ := h (rankMember f p hp) hp
    exact ZFSet.mem_prod.mpr ⟨a.val, ha, b.val, hb,
      (rankIsOrderedPair_iff hl _ _ _).mp he⟩
  · intro h p hp
    obtain ⟨a, ha, b, hb, he⟩ := ZFSet.mem_prod.mp (h hp)
    exact ⟨rankMember x a ha, rankMember y b hb, ha, hb,
      (rankIsOrderedPair_iff hl _ _ _).mpr he⟩

def rankGraphApplies {lambda : Ordinal.{u}} (f a b : RankDomain lambda) : Prop :=
  ∃ p : RankDomain lambda, p.val ∈ f.val ∧ rankIsOrderedPair p a b

theorem rankGraphApplies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (f a b : RankDomain lambda) :
    rankGraphApplies f a b ↔ ZFSet.pair a.val b.val ∈ f.val := by
  constructor
  · rintro ⟨p, hp, he⟩
    rwa [(rankIsOrderedPair_iff hl _ _ _).mp he] at hp
  · intro hp
    exact ⟨rankOrderedPair hl a b, hp, (rankIsOrderedPair_iff hl _ _ _).mpr rfl⟩

def rankIsFunction {lambda : Ordinal.{u}} (f x y : RankDomain lambda) : Prop :=
  rankGraphBetween f x y ∧ ∀ a : RankDomain lambda, a.val ∈ x.val →
    ∃ b : RankDomain lambda, b.val ∈ y.val ∧ rankGraphApplies f a b ∧
      ∀ c : RankDomain lambda, rankGraphApplies f a c → c = b

theorem rankIsFunction_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (f x y : RankDomain lambda) : rankIsFunction f x y ↔ ZFSet.IsFunc x.val y.val f.val := by
  constructor
  · rintro ⟨hg, ht⟩
    have hg' := (rankGraphBetween_iff hl f x y).mp hg
    refine ⟨hg', ?_⟩
    intro a ha
    obtain ⟨b, hb, hab, hu⟩ := ht (rankMember x a ha) ha
    refine ⟨b.val, (rankGraphApplies_iff hl _ _ _).mp hab, ?_⟩
    intro c hc
    have hcy := (ZFSet.pair_mem_prod.mp (hg' hc)).2
    have he := hu (rankMember y c hcy) ((rankGraphApplies_iff hl _ _ _).mpr hc)
    exact congrArg Subtype.val he
  · rintro ⟨hg, ht⟩
    refine ⟨(rankGraphBetween_iff hl f x y).mpr hg, ?_⟩
    intro a ha
    obtain ⟨b, hb, hu⟩ := ht a.val ha
    have hby := (ZFSet.pair_mem_prod.mp (hg hb)).2
    refine ⟨rankMember y b hby, hby, (rankGraphApplies_iff hl _ _ _).mpr hb, ?_⟩
    intro c hc
    exact Subtype.ext (hu c.val ((rankGraphApplies_iff hl _ _ _).mp hc))

end FullMarkedBLP

