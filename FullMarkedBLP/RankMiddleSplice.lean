import FullMarkedBLP.RankApplicationLowTail

namespace FullMarkedBLP

theorem rankAgreement_comp_right {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {left right : RankElementaryEmbedding lambda} {delta : OrdinalDomain lambda}
    (limit : Order.IsSuccLimit delta.val) (agreement : rankCutoffAgreement delta.val left right)
    (inner : RankElementaryEmbedding lambda) :
    rankCutoffAgreement delta.val (left.comp inner) (right.comp inner) := by
  intro x z hx _
  exact rankAgreement_all_inputs hl limit agreement x (inner z) hx

theorem rankApply_agrees_with_composition {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda}
    (critical : RankCriticalPoint j c) (owner : RankElementaryEmbedding lambda) :
    rankCutoffAgreement (rankOrdinalAction (rankApply hl j owner) c).val
      (rankApply hl j owner) (j.comp owner) := by
  let identity := FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage (RankDomain lambda)
  have fixed : rankCutoffAgreement c.val identity j := by
    intro x z _ hz
    change x.val ∈ z.val ↔ x.val ∈ (j z).val
    rw [rankCriticalPoint_fixes_rank hl critical hz]
  have result := rankAgreement_comp_left hl (rankApply hl j owner)
    (rankCriticalPoint_isSuccLimit hl critical) fixed
  intro x z hx hz
  have point := result x z hx hz
  change x.val ∈ (rankApply hl j owner z).val ↔ x.val ∈ (rankApply hl j owner (j z)).val at point
  rw [rankApply_on_image] at point
  exact point

/-- The three cutoff bounds needed for the guarded middle splice are kept
explicit. Concrete word and position lemmas must supply each of them. -/
theorem rankApply_middle_certificate {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda}
    (critical : RankCriticalPoint j c) (owner front tail bridge : RankElementaryEmbedding lambda)
    {delta eta output : OrdinalDomain lambda} (deltaLimit : Order.IsSuccLimit delta.val)
    (etaLimit : Order.IsSuccLimit eta.val)
    (oldCertificate : rankCutoffAgreement delta.val owner (front.comp tail))
    (bridgeCertificate : rankCutoffAgreement eta.val j bridge)
    (ownerBound : output ≤ rankOrdinalAction (rankApply hl j owner) c)
    (oldBound : output ≤ rankOrdinalAction j delta)
    (bridgeBound : output ≤ rankOrdinalAction (rankApply hl j front) eta) :
    rankCutoffAgreement output.val (rankApply hl j owner)
      ((rankApply hl j front).comp (bridge.comp tail)) := by
  have ownerTransfer := rankApply_agrees_with_composition hl critical owner
  have oldTransfer := rankAgreement_comp_left hl j deltaLimit oldCertificate
  have bridgeTail := rankAgreement_comp_right hl etaLimit bridgeCertificate tail
  have bridgeTransfer := rankAgreement_comp_left hl (rankApply hl j front) etaLimit bridgeTail
  intro x z hx hz
  have first := ownerTransfer x z (hx.trans_le ownerBound) (hz.trans_le ownerBound)
  have second := oldTransfer x z (hx.trans_le oldBound) (hz.trans_le oldBound)
  have third := bridgeTransfer x z (hx.trans_le bridgeBound) (hz.trans_le bridgeBound)
  change x.val ∈ (rankApply hl j front (j (tail z))).val ↔
    x.val ∈ (rankApply hl j front (bridge (tail z))).val at third
  rw [rankApply_on_image] at third
  exact first.trans (second.trans third)

end FullMarkedBLP
