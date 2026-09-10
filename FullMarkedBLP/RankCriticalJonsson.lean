import FullMarkedBLP.RankCriticalPower
import FullMarkedBLP.CardinalOmegaJonsson

namespace FullMarkedBLP

/-- An actual omega-Jonsson coloring of the von Neumann set at the critical
supremum. The coloring is constructed externally; its later graph encoding
and elementarity transfer still require the supremum to lie below lambda. -/
theorem rankCriticalSupremum_omegaJonsson {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    ∃ color : (Nat → (rankCriticalSupremum j critical).toZFSet) →
      (rankCriticalSupremum j critical).toZFSet, IsOmegaJonsson color := by
  let mu := rankCriticalSupremum j critical
  letI : Nonempty mu.toZFSet := ⟨⟨Ordinal.toZFSet 0,
    Ordinal.toZFSet_mem_toZFSet_iff.mpr (rankCriticalSupremum_isSuccLimit cp).pos⟩⟩
  apply exists_omegaJonsson_of_countable_power
  · rw [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet]
    have bound := (rankCriticalSupremum_uncountable hl cp).le
    simpa only [Cardinal.lift_aleph0] using (Cardinal.lift_le.{u + 1}.mpr bound)
  · rw [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet]
    have equation := congrArg Cardinal.lift.{u + 1} (rankCriticalSupremum_countable_power hl cp)
    simpa only [Cardinal.lift_power, Cardinal.lift_aleph0, Cardinal.lift_ofNat] using equation

end FullMarkedBLP
