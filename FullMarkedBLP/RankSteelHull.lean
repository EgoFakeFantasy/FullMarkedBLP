import FullMarkedBLP.RankOrdinalFunction
import FullMarkedBLP.RankHierarchyImage

namespace FullMarkedBLP

/-- The literal ordinal-value condition in Steel's hull: f and s lie in
V_alpha, f is ordinal-valued, and k(f) takes s to the proposed value. -/
def RankSteelHullMember {lambda : Ordinal.{u}} (k : RankElementaryEmbedding lambda)
    (alpha : OrdinalDomain lambda) (value : ZFSet.{u}) : Prop :=
  ∃ f s : RankDomain lambda, f.val.rank < alpha.val ∧ s.val.rank < alpha.val ∧
    RankOrdinalFunction f ∧ ZFSet.pair s.val value ∈ (k f).val

theorem rankSteelHullMember_bound {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) {value : ZFSet.{u}}
    (member : RankSteelHullMember k alpha value) :
    value ∈ (ordinalDomainElement (rankOrdinalAction k alpha)).val := by
  obtain ⟨f, s, hf, _, function, edge⟩ := member
  have ordinal := rankOrdinalFunction_value hl ((rankElementary_ordinalFunction_iff k f).mpr function) edge
  have rankBound : value.rank < (rankOrdinalAction k alpha).val := by
    have bound := rank_graph_value_lt edge
    rw [rankElementary_rank hl k f] at bound
    exact bound.trans ((rankOrdinalAction_strictMono k) hf)
  change value ∈ (rankOrdinalAction k alpha).val.toZFSet
  rw [← ordinal.toZFSet_rank_eq]
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr rankBound

/-- Steel's hull is an actual set in V_lambda. Its a priori ordinal bound
comes from exact rank preservation by the actual embedding. -/
noncomputable def rankSteelHull {lambda : Ordinal.{u}} (_hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.sep (RankSteelHullMember k alpha) (ordinalDomainElement (rankOrdinalAction k alpha)).val, by
    exact (ZFSet.rank_mono (show
      ZFSet.sep (RankSteelHullMember k alpha) (ordinalDomainElement (rankOrdinalAction k alpha)).val ⊆
        (ordinalDomainElement (rankOrdinalAction k alpha)).val from
      fun _ h => (ZFSet.mem_sep.mp h).1)).trans_lt (ordinalDomainElement (rankOrdinalAction k alpha)).property⟩

theorem rankSteelHull_mem {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) (value : ZFSet.{u}) :
    value ∈ (rankSteelHull hl k alpha).val ↔ RankSteelHullMember k alpha value := by
  exact ZFSet.mem_sep.trans ⟨And.right, fun h => ⟨rankSteelHullMember_bound hl k alpha h, h⟩⟩

theorem rankSteelHull_subset_ordinal {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    (rankSteelHull hl k alpha).val ⊆ (ordinalDomainElement (rankOrdinalAction k alpha)).val :=
  fun _ h => rankSteelHullMember_bound hl k alpha ((rankSteelHull_mem hl k alpha _).mp h)

theorem rankSteelHull_member_ordinal {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) {value : ZFSet.{u}}
    (member : value ∈ (rankSteelHull hl k alpha).val) : ZFSet.IsOrdinal value :=
  (ZFSet.isOrdinal_toZFSet _).mem (rankSteelHull_subset_ordinal hl k alpha member)

theorem rankSteelHull_mono {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) {alpha beta : OrdinalDomain lambda} (bound : alpha ≤ beta) :
    (rankSteelHull hl k alpha).val ⊆ (rankSteelHull hl k beta).val := by
  intro value member
  obtain ⟨f, s, hf, hs, function, edge⟩ := (rankSteelHull_mem hl k alpha value).mp member
  exact (rankSteelHull_mem hl k beta value).mpr
    ⟨f, s, hf.trans_le bound, hs.trans_le bound, function, edge⟩

end FullMarkedBLP
