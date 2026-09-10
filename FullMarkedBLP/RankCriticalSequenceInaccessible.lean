import FullMarkedBLP.RankCriticalInaccessible
import FullMarkedBLP.RankCriticalSequence

namespace FullMarkedBLP

/-- The successive right arguments in repeated application by j. Their
critical points are precisely the successive ordinary critical images. -/
noncomputable def rankCriticalSequenceEmbedding {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda) :
    Nat → RankElementaryEmbedding lambda
  | 0 => j
  | n + 1 => rankApply hl j (rankCriticalSequenceEmbedding hl j n)

theorem rankCriticalSequenceEmbedding_criticalPoint {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) (n : Nat) :
    RankCriticalPoint (rankCriticalSequenceEmbedding hl j n) (rankCriticalSequence j critical n) := by
  induction n with
  | zero => exact cp
  | succ n ih => exact rankApply_criticalPoint hl j ih

theorem rankCriticalSequence_isInaccessible {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) (n : Nat) :
    Cardinal.IsInaccessible (rankCriticalSequence j critical n).val.card :=
  rankCriticalPoint_isInaccessible hl (rankCriticalSequenceEmbedding_criticalPoint hl cp n)

/-- The small hierarchy-size estimate used in the Steel hull construction.
It follows directly from low-rank fixedness and the transported-surjection
contradiction, without a separate cardinal hierarchy calculation. -/
theorem rankCriticalPoint_hierarchy_card_lt {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (alpha : OrdinalDomain lambda) (below : alpha < critical) :
    (rankHierarchy alpha).val.card < critical.val.card := by
  apply rankCriticalPoint_low_rank_card_lt hl cp
  simpa only [rankHierarchy, ZFSet.rank_vonNeumann] using below

theorem rankCriticalSequence_hierarchy_card_lt {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) (n : Nat)
    (alpha : OrdinalDomain lambda) (below : alpha < rankCriticalSequence j critical n) :
    (rankHierarchy alpha).val.card < (rankCriticalSequence j critical n).val.card :=
  rankCriticalPoint_hierarchy_card_lt hl (rankCriticalSequenceEmbedding_criticalPoint hl cp n) alpha below

end FullMarkedBLP
