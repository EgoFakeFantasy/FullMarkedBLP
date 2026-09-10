import FullMarkedBLP.RankGraphClosure

namespace FullMarkedBLP

theorem rank_orderedPair_lt_of_limit {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {x y : ZFSet.{u}} (hx : x.rank < lambda) (hy : y.rank < lambda) :
    (ZFSet.pair x y).rank < lambda := by
  rw [ZFSet.pair, ZFSet.rank_pair, ZFSet.rank_singleton, ZFSet.rank_pair]
  exact max_lt (hl.succ_lt (hl.succ_lt hx))
    (hl.succ_lt (max_lt (hl.succ_lt hx) (hl.succ_lt hy)))

noncomputable def rankOrderedPair {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y : RankDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.pair x.val y.val, rank_orderedPair_lt_of_limit hl x.property y.property⟩

theorem rankOrderedPair_inj {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y x' y' : RankDomain lambda) :
    rankOrderedPair hl x y = rankOrderedPair hl x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro he
    have hh := ZFSet.pair_inj.mp (congrArg Subtype.val he)
    exact ⟨Subtype.ext hh.1, Subtype.ext hh.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem rankOrderedPair_mem_graph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y f : RankDomain lambda) :
    (rankOrderedPair hl x y).val ∈ f.val ↔ ZFSet.pair x.val y.val ∈ f.val := Iff.rfl

end FullMarkedBLP
