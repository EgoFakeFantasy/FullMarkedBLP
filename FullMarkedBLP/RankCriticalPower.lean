import FullMarkedBLP.RankCriticalSupremumFixed

namespace FullMarkedBLP

/-- The critical supremum is the cardinal sum of its countable cofinal
sequence of initial ordinals. -/
theorem rankCriticalSupremum_cardinal_sum {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    Cardinal.sum (fun n => (rankCriticalSequence j critical n).val.card) =
      (rankCriticalSupremum j critical).card := by
  let cards := fun n => (rankCriticalSequence j critical n).val.card
  let total := (rankCriticalSupremum j critical).card
  have infinite : Cardinal.aleph0 ≤ total := (rankCriticalSupremum_uncountable hl cp).le
  apply le_antisymm
  · have bound := Cardinal.sum_le_sum cards (fun _ => total) (fun n =>
      Ordinal.card_le_card (rankCriticalSequence_lt_supremum cp n).le)
    have constant : Cardinal.sum (fun _ : Nat => total) = total := by
      rw [Cardinal.sum_const]
      simp only [Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
      exact Cardinal.mul_eq_right infinite infinite Cardinal.aleph0_ne_zero
    exact bound.trans_eq constant
  · apply Cardinal.ord_le_ord.mp
    rw [rankCriticalSupremum_cardinal hl cp]
    apply Ordinal.iSup_le
    intro n
    obtain ⟨c, hc⟩ := rankCriticalSequence_cardinal hl cp n
    have same : (cards n).ord = (rankCriticalSequence j critical n).val := by
      change (rankCriticalSequence j critical n).val.card.ord = _
      rw [← hc, Cardinal.card_ord]
    rw [← same]
    exact Cardinal.ord_le_ord.mpr (Cardinal.le_sum cards n)

/-- The singular strong-limit cardinal at the critical supremum satisfies
the cardinal arithmetic used in Kunen's direct omega-Jonsson construction. -/
theorem rankCriticalSupremum_countable_power {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    (rankCriticalSupremum j critical).card ^ Cardinal.aleph0 =
      2 ^ (rankCriticalSupremum j critical).card := by
  let total := (rankCriticalSupremum j critical).card
  let cards := fun n => (rankCriticalSequence j critical n).val.card
  have infinite : Cardinal.aleph0 ≤ total := (rankCriticalSupremum_uncountable hl cp).le
  have strong := rankCriticalSupremum_isStrongLimit hl cp
  apply le_antisymm
  · exact (Cardinal.power_le_power_left strong.ne_zero infinite).trans_eq
      (Cardinal.power_self_eq infinite)
  · have smaller : ∀ n, cards n < total := by
      intro n
      rw [← Cardinal.ord_lt_ord, rankCriticalSupremum_cardinal hl cp]
      obtain ⟨c, hc⟩ := rankCriticalSequence_cardinal hl cp n
      change (rankCriticalSequence j critical n).val.card.ord < _
      rw [← hc, Cardinal.card_ord, hc]
      exact rankCriticalSequence_lt_supremum cp n
    calc
      2 ^ total = 2 ^ Cardinal.sum cards := by rw [rankCriticalSupremum_cardinal_sum hl cp]
      _ = Cardinal.prod (fun n => 2 ^ cards n) := Cardinal.power_sum 2 cards
      _ ≤ Cardinal.prod (fun _ : Nat => total) :=
        Cardinal.prod_le_prod _ _ (fun n => (strong.isStrongPrelimit (smaller n)).le)
      _ = total ^ Cardinal.aleph0 := by
        simp only [Cardinal.prod_const, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]

end FullMarkedBLP
