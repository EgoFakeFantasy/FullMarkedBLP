import FullMarkedBLP.RankSteelEvaluation

namespace FullMarkedBLP

/-- A set of ordinals, with its order type kept in the universe of the set. -/
structure ZFOrdinalCollection where
  carrier : ZFSet.{u}
  ordinal : ∀ x ∈ carrier, ZFSet.IsOrdinal x

namespace ZFOrdinalCollection

noncomputable def key (s : ZFOrdinalCollection.{u}) (a : Shrink.{u} s.carrier) : Ordinal.{u} :=
  ((equivShrink s.carrier).symm a).val.rank

theorem key_injective (s : ZFOrdinalCollection.{u}) : Function.Injective s.key := by
  intro a b same
  apply (equivShrink s.carrier).symm.injective
  apply Subtype.ext
  exact (ZFSet.IsOrdinal.rank_inj (s.ordinal _ ((equivShrink s.carrier).symm a).property)
    (s.ordinal _ ((equivShrink s.carrier).symm b).property)).mp same

def relation (s : ZFOrdinalCollection.{u}) (a b : Shrink.{u} s.carrier) : Prop := s.key a < s.key b

instance (s : ZFOrdinalCollection.{u}) : IsWellOrder (Shrink.{u} s.carrier) s.relation :=
  Function.Injective.isWellOrder (· < ·) s.key_injective

noncomputable def orderType (s : ZFOrdinalCollection.{u}) : Ordinal.{u} := Ordinal.type s.relation

theorem orderType_card (s : ZFOrdinalCollection.{u}) : s.orderType.card = s.carrier.card :=
  Ordinal.card_type s.relation

noncomputable def position (s : ZFOrdinalCollection.{u}) (a : s.carrier) : Ordinal.{u} :=
  Ordinal.typein s.relation (equivShrink s.carrier a)

theorem position_lt (s : ZFOrdinalCollection.{u}) (a : s.carrier) : s.position a < s.orderType :=
  Ordinal.typein_lt_type s.relation _

theorem position_lt_iff (s : ZFOrdinalCollection.{u}) (a b : s.carrier) :
    s.position a < s.position b ↔ a.val ∈ b.val := by
  rw [position, position, Ordinal.typein_lt_typein]
  change ((equivShrink s.carrier).symm (equivShrink s.carrier a)).val.rank <
    ((equivShrink s.carrier).symm (equivShrink s.carrier b)).val.rank ↔ _
  simp only [Equiv.symm_apply_apply]
  exact (s.ordinal _ a.property).rank_lt_iff_mem (s.ordinal _ b.property)

noncomputable def collapse (s : ZFOrdinalCollection.{u}) : s.carrier → s.orderType.toZFSet :=
  fun a => ⟨(s.position a).toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr (s.position_lt a)⟩

theorem collapse_mem_iff (s : ZFOrdinalCollection.{u}) (a b : s.carrier) :
    (s.collapse a).val ∈ (s.collapse b).val ↔ a.val ∈ b.val :=
  Ordinal.toZFSet_mem_toZFSet_iff.trans (s.position_lt_iff a b)

end ZFOrdinalCollection

noncomputable def rankSteelHullCollection {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) : ZFOrdinalCollection.{u} :=
  ⟨(rankSteelHull hl k alpha).val, fun _ h => rankSteelHull_member_ordinal hl k alpha h⟩

noncomputable def rankSteelOrderType {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) : Ordinal.{u} :=
  (rankSteelHullCollection hl k alpha).orderType

theorem rankSteelOrderType_lt_critical {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda)
    {owner : RankElementaryEmbedding lambda} {gamma : OrdinalDomain lambda}
    (cp : RankCriticalPoint owner gamma) (below : alpha < gamma) :
    rankSteelOrderType hl k alpha < gamma.val := by
  obtain ⟨c, hc⟩ := rankCriticalPoint_isCardinal hl cp
  rw [← hc, Cardinal.lt_ord]
  have small := rankSteelHull_card_lt_critical hl k alpha cp below
  rw [← hc, Cardinal.card_ord] at small
  exact ((rankSteelHullCollection hl k alpha).orderType_card.le).trans_lt small

end FullMarkedBLP
