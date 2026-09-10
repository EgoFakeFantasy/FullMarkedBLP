import FullMarkedBLP.RankCriticalRegular
import FullMarkedBLP.RankOmegaPreservation

namespace FullMarkedBLP

theorem rankCriticalPoint_omega_lt {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    Ordinal.omega0 < critical.val := by
  have lower := Ordinal.omega0_le_of_isSuccLimit (rankCriticalPoint_isSuccLimit hl cp)
  apply lt_of_le_of_ne lower
  intro equal
  have hw : Ordinal.omega0 < lambda := lower.trans_lt critical.property
  have same : critical = ⟨Ordinal.omega0, hw⟩ := Subtype.ext equal.symm
  apply cp.1
  rw [same]
  exact rankOrdinalAction_omega hw j

/-- Inaccessibility of the critical cardinal is derived from actual
elementarity, with no regularity or strong-limit premise. -/
theorem rankCriticalPoint_isInaccessible {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    Cardinal.IsInaccessible critical.val.card := by
  apply Cardinal.isInaccessible_def.mpr
  refine ⟨?_, rankCriticalPoint_isRegular hl cp, rankCriticalPoint_isStrongLimit hl cp⟩
  obtain ⟨c, hc⟩ := rankCriticalPoint_isCardinal hl cp
  have cardEq : critical.val.card = c := by rw [← hc, Cardinal.card_ord]
  rw [cardEq, ← Cardinal.ord_lt_ord, Cardinal.ord_aleph0, hc]
  exact rankCriticalPoint_omega_lt hl cp

end FullMarkedBLP
