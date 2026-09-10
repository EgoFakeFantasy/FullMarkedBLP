import FullMarkedBLP.RankCriticalCardinal

namespace FullMarkedBLP

/-- Ordinary iteration of the actual ordinal action from a critical point. -/
noncomputable def rankCriticalSequence {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (critical : OrdinalDomain lambda) : Nat → OrdinalDomain lambda
  | 0 => critical
  | n + 1 => rankOrdinalAction j (rankCriticalSequence j critical n)

theorem rankCriticalSequence_strictMono {lambda : Ordinal.{u}} {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    StrictMono (rankCriticalSequence j critical) := by
  apply strictMono_nat_of_lt_succ
  intro n
  induction n with
  | zero => exact rankCriticalPoint_lt_image cp
  | succ n ih => exact rankOrdinalAction_strictMono j ih

theorem rankCriticalSequence_cardinal {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) (n : Nat) :
    ∃ c : Cardinal.{u}, c.ord = (rankCriticalSequence j critical n).val := by
  induction n with
  | zero => exact rankCriticalPoint_isCardinal hl cp
  | succ n ih => exact (rankOrdinalAction_cardinal_iff hl j _).mpr ih

theorem rankCriticalSequence_double {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (critical : OrdinalDomain lambda) (n : Nat) :
    rankOrdinalAction (j.comp j) (rankCriticalSequence j critical n) = rankCriticalSequence j critical (n + 2) := by
  rw [rankOrdinalAction_comp]
  rfl

theorem rankCriticalSequence_applied_double {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (critical : OrdinalDomain lambda) (n : Nat) :
    rankOrdinalAction (rankApply hl (j.comp j) (j.comp j)) (rankCriticalSequence j critical (n + 2)) =
      rankCriticalSequence j critical (n + 4) := by
  rw [← rankCriticalSequence_double j critical n, rankApply_ordinal_image,
    rankCriticalSequence_double, rankCriticalSequence_double]

end FullMarkedBLP
