import FullMarkedBLP.NativeCardinalObligation

namespace FullMarkedBLP

/-- Function graphs between sets in a limit rank domain remain in that domain. -/
theorem rank_graph_lt_of_limit {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {x y f : ZFSet.{u}} (hx : x.rank < lambda) (hy : y.rank < lambda)
    (hf : f ⊆ ZFSet.prod x y) : f.rank < lambda := by
  have hp : ZFSet.prod x y ⊆ ZFSet.powerset (ZFSet.powerset (x ∪ y)) := by
    intro z hz
    change z ∈ ZFSet.pairSep (fun _ _ => True) x y at hz
    exact (ZFSet.mem_sep.mp hz).1
  have hb := ZFSet.rank_mono (show f ⊆ ZFSet.powerset (ZFSet.powerset (x ∪ y)) from
    fun z hz => hp (hf hz))
  simp only [ZFSet.rank_powerset, ZFSet.rank_union] at hb
  exact lt_of_le_of_lt hb (hl.succ_lt (hl.succ_lt (max_lt hx hy)))

theorem rank_function_lt_of_limit {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {x y f : ZFSet.{u}} (hx : x.rank < lambda) (hy : y.rank < lambda)
    (hf : ZFSet.IsFunc x y f) : f.rank < lambda :=
  rank_graph_lt_of_limit hl hx hy hf.1

end FullMarkedBLP
