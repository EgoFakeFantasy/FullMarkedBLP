import FullMarkedBLP.RankSteelStrictDecrease
import FullMarkedBLP.RankWellFoundedReduction

namespace FullMarkedBLP

/-- Steel's bounded-application theorem on the actual common rank domain.
No well-foundedness premise or additional embedding axiom is used. -/
theorem rankBoundedApplication_wellFounded {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (bound : OrdinalDomain lambda) :
    WellFounded (RankBoundedApplication hl bound) := by
  classical
  by_cases existsCritical : ∃ j : RankElementaryEmbedding lambda,
      ∃ critical : OrdinalDomain lambda, RankCriticalPoint j critical
  · obtain ⟨j, critical, cp⟩ := existsCritical
    obtain ⟨gamma, above, _, owner, cpGamma, _⟩ := rankDomain_inaccessible_above hl cp bound
    apply (InvImage.wf (fun k : RankElementaryEmbedding lambda => rankSteelOrderType hl k gamma)
      Ordinal.lt_wf).mono
    intro child parent step
    obtain ⟨right, critical, same, cpParent, below⟩ := step
    change rankSteelOrderType hl child gamma < rankSteelOrderType hl parent gamma
    rw [same]
    exact rankSteelOrderType_apply_lt hl parent right cpGamma cpParent (below.trans above)
  · refine ⟨fun parent => Acc.intro parent ?_⟩
    intro child step
    obtain ⟨_, critical, _, cp, _⟩ := step
    exact False.elim (existsCritical ⟨parent, critical, cp⟩)

theorem rankTerminalDescent_wellFounded_actual {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) : WellFounded (RankTerminalDescent hl) :=
  rankTerminalDescent_wellFounded hl (rankBoundedApplication_wellFounded hl)

/-- Every fully realized literal pattern has well-founded expansion,
using the proved same-domain Steel theorem. -/
theorem rankFullMarkedRealization_accessible_actual {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda}
    (realization : RankFullMarkedRealization a theta embedding) :
    Acc (fun child parent => Step parent child) a :=
  rankFullMarkedRealization_accessible hl (rankTerminalDescent_wellFounded_actual hl) realization

/-- Only the full root realization remains as an input to expansion
well-foundedness. Deriving that realization from I2 is a separate obligation;
this theorem does not assert the final short-key comparison well-order. -/
theorem generatedStep_wellFounded_of_root {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda)
    {rootTheta : Nat → OrdinalDomain lambda} {rootEmbedding : Nat → RankElementaryEmbedding lambda}
    (root : RankFullMarkedRealization start rootTheta rootEmbedding) :
    WellFounded (fun (child parent : {a : Pattern // Generated a}) => Step parent.val child.val) :=
  generatedStep_wellFounded_of_root_and_bounded hl (rankBoundedApplication_wellFounded hl) root

end FullMarkedBLP
