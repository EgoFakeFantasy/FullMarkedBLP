import FullMarkedBLP.RankCriticalSupremum
import FullMarkedBLP.RankCountableContinuity

namespace FullMarkedBLP

/-- If the critical supremum is inside the domain, it is fixed. This is the
fixed-point step in Kunen's contradiction; it does not assume or assert the
unproved conclusion that the supremum equals the domain height. -/
theorem rankCriticalSupremum_fixed_of_lt {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (inside : rankCriticalSupremum j critical < lambda) :
    rankOrdinalAction j ⟨rankCriticalSupremum j critical, inside⟩ =
      ⟨rankCriticalSupremum j critical, inside⟩ := by
  let beta : OrdinalDomain lambda := ⟨rankCriticalSupremum j critical, inside⟩
  let sequence : Nat → Set.Iio beta.val :=
    fun n => ⟨(rankCriticalSequence j critical n).val, rankCriticalSequence_lt_supremum cp n⟩
  have cofinal : ∀ b < beta.val, ∃ n, b < (sequence n).val := by
    intro b hb
    exact rankCriticalSupremum_cofinal j critical hb
  have imageCofinal := rankOrdinalAction_cofinal_nat hl cp beta sequence cofinal
  apply le_antisymm
  · apply le_of_not_gt
    intro above
    obtain ⟨n, hn⟩ := imageCofinal beta.val above
    change rankCriticalSupremum j critical < (rankCriticalSequence j critical (n + 1)).val at hn
    exact (lt_irrefl _) (hn.trans (rankCriticalSequence_lt_supremum cp (n + 1)))
  · exact rankOrdinalAction_le_self_image j beta

theorem rankCriticalSupremum_uncountable {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    Cardinal.aleph0 < (rankCriticalSupremum j critical).card := by
  rw [← Cardinal.ord_lt_ord, Cardinal.ord_aleph0, rankCriticalSupremum_cardinal hl cp]
  exact (rankCriticalPoint_omega_lt hl cp).trans (rankCriticalSequence_lt_supremum cp 0)

theorem rankCriticalSupremum_not_regular {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    ¬Cardinal.IsRegular (rankCriticalSupremum j critical).card := by
  intro regular
  have bound := regular.le_cof_ord
  rw [rankCriticalSupremum_cardinal hl cp, rankCriticalSupremum_cof cp] at bound
  exact (not_le_of_gt (rankCriticalSupremum_uncountable hl cp)) bound

end FullMarkedBLP
