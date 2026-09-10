import FullMarkedBLP.RankOrderedPair

namespace FullMarkedBLP

def rankIsUnorderedPair {lambda : Ordinal.{u}} (z x y : RankDomain lambda) : Prop :=
  ∀ w : RankDomain lambda, w.val ∈ z.val ↔ w = x ∨ w = y

theorem rankIsUnorderedPair_iff {lambda : Ordinal.{u}} (z x y : RankDomain lambda) :
    rankIsUnorderedPair z x y ↔ z.val = {x.val, y.val} := by
  constructor
  · intro h
    apply ZFSet.ext
    intro w
    constructor
    · intro hw
      rcases (h (rankMember z w hw)).mp hw with he | he
      · have := congrArg Subtype.val he
        simp only [rankMember] at this
        simp [this]
      · have := congrArg Subtype.val he
        simp only [rankMember] at this
        simp [this]
    · intro hw
      rcases ZFSet.mem_pair.mp hw with he | he
      · subst w
        exact (h x).mpr (Or.inl rfl)
      · subst w
        exact (h y).mpr (Or.inr rfl)
  · intro h w
    rw [h, ZFSet.mem_pair]
    exact or_congr Subtype.val_inj Subtype.val_inj

noncomputable def rankUnorderedPair {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y : RankDomain lambda) : RankDomain lambda :=
  ⟨{x.val, y.val}, by
    rw [ZFSet.rank_pair]
    exact max_lt (hl.succ_lt x.property) (hl.succ_lt y.property)⟩

def rankIsOrderedPair {lambda : Ordinal.{u}} (z x y : RankDomain lambda) : Prop :=
  ∃ s t : RankDomain lambda,
    rankIsUnorderedPair s x x ∧ rankIsUnorderedPair t x y ∧ rankIsUnorderedPair z s t

theorem rankIsOrderedPair_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (z x y : RankDomain lambda) :
    rankIsOrderedPair z x y ↔ z.val = ZFSet.pair x.val y.val := by
  constructor
  · rintro ⟨s, t, hs, ht, hz⟩
    rw [rankIsUnorderedPair_iff] at hs ht hz
    rw [hz, hs, ht]
    simp [ZFSet.pair]
  · intro hz
    refine ⟨rankUnorderedPair hl x x, rankUnorderedPair hl x y, ?_, ?_, ?_⟩
    · exact (rankIsUnorderedPair_iff _ _ _).mpr rfl
    · exact (rankIsUnorderedPair_iff _ _ _).mpr rfl
    · apply (rankIsUnorderedPair_iff _ _ _).mpr
      simpa [rankUnorderedPair, ZFSet.pair] using hz

end FullMarkedBLP
