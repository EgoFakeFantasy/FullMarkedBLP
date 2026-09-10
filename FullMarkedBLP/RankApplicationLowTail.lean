import FullMarkedBLP.RankAgreementComposition
import FullMarkedBLP.RankApplicationBelowCritical
import FullMarkedBLP.RankApplicationAgreement
import FullMarkedBLP.RankCriticalLimit

namespace FullMarkedBLP

/-- A low tail can be restored after an arbitrary applied prefix, with
the weak agreement transported through that prefix. -/
theorem rankApply_low_tail {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda}
    (critical : RankCriticalPoint j c) (front tail : RankElementaryEmbedding lambda) :
    rankCutoffAgreement (rankOrdinalAction (rankApply hl j front) c).val
      (rankApply hl j (front.comp tail)) ((rankApply hl j front).comp tail) := by
  rw [rankApply_comp_right]
  exact rankAgreement_comp_left hl (rankApply hl j front) (rankCriticalPoint_isSuccLimit hl critical)
    (rankApply_agrees_below_critical hl critical tail)

/-- Transfer a historical certificate while keeping the low tail unchanged.
The resulting cutoff is the applied prefix evaluated at the low tail's
cutoff; it may be strictly smaller than the image of the historical cutoff. -/
theorem rankApply_low_tail_certificate {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda}
    (critical : RankCriticalPoint j c) (owner front tail : RankElementaryEmbedding lambda)
    {epsilon : OrdinalDomain lambda} (below : epsilon ≤ c)
    (certificate : rankCutoffAgreement (rankOrdinalAction front epsilon).val owner (front.comp tail)) :
    rankCutoffAgreement (rankOrdinalAction (rankApply hl j front) epsilon).val
      (rankApply hl j owner) ((rankApply hl j front).comp tail) := by
  have transferred := rankApply_cutoffAgreement hl j certificate
  have replacement := rankApply_low_tail hl critical front tail
  have oldBound : rankOrdinalAction (rankApply hl j front) epsilon ≤
      rankOrdinalAction j (rankOrdinalAction front epsilon) := by
    rw [← rankApply_ordinal_image hl j front epsilon]
    exact rankOrdinalAction_monotone _ (rankOrdinalAction_le_self_image j epsilon)
  have replacementBound := rankOrdinalAction_monotone (rankApply hl j front) below
  intro x z hx hz
  exact (transferred x z (hx.trans_le oldBound) (hz.trans_le oldBound)).trans
    (replacement x z (hx.trans_le replacementBound) (hz.trans_le replacementBound))

end FullMarkedBLP
