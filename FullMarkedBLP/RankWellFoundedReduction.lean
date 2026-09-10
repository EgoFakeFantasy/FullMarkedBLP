import FullMarkedBLP.BoundedApplicationStep

namespace FullMarkedBLP

/-- Once actual bounded application is well founded at every bound,
ordinal descent combined with finite nonempty application descent is well
founded. This is only the logical reduction; it does not prove Steel. -/
theorem rankTerminalDescent_wellFounded {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda)
    (bounded : ∀ bound : OrdinalDomain lambda, WellFounded (RankBoundedApplication hl bound)) :
    WellFounded (RankTerminalDescent hl) := by
  have all : ∀ bound : OrdinalDomain lambda, ∀ owner : RankElementaryEmbedding lambda,
      Acc (RankTerminalDescent hl) (bound, owner) := by
    intro bound
    induction bound using (wellFounded_lt : WellFounded ((· < ·) : OrdinalDomain lambda → OrdinalDomain lambda → Prop)).induction with
    | h bound lower =>
      intro owner
      induction owner using (bounded bound).transGen.induction with
      | h owner previous =>
        refine Acc.intro _ ?_
        rintro ⟨childBound, childOwner⟩ step
        rcases step with smaller | ⟨same, chain⟩
        · exact lower childBound smaller childOwner
        · change childBound = bound at same
          subst childBound
          exact previous childOwner chain
  exact ⟨fun point => all point.1 point.2⟩

/-- Accessibility is proved for EVERY realized pattern and assignment,
so child realizations may be the actual semantic lifts of their parents.
No independent finite-root choices or global ranking choice is used. -/
theorem rankFullMarkedRealization_accessible {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (wf : WellFounded (RankTerminalDescent hl))
    {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankFullMarkedRealization a theta embedding) : Acc (fun child parent => Step parent child) a := by
  have all : ∀ point : OrdinalDomain lambda × RankElementaryEmbedding lambda,
      ∀ (a : Pattern) (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda),
        RankFullMarkedRealization a theta embedding →
        (theta (a.length + 1), embedding a.length) = point →
        Acc (fun child parent => Step parent child) a := by
    intro point
    induction point using wf.induction with
    | h point previous =>
      intro a theta embedding realization atPoint
      refine Acc.intro _ ?_
      intro child step
      obtain ⟨newTheta, newEmbedding, result, _, descent⟩ :=
        rankFullMarkedRealization_step_bounded hl realization step
      rw [atPoint] at descent
      exact previous _ descent child newTheta newEmbedding result rfl
  exact all _ a theta embedding h rfl

/-- A modular reduction of generated expansion well-foundedness to a full
root realization and bounded application. RankSteelWellFounded proves the
latter input and supplies generatedStep_wellFounded_of_root. -/
theorem generatedStep_wellFounded_of_root_and_bounded {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda)
    (bounded : ∀ bound : OrdinalDomain lambda, WellFounded (RankBoundedApplication hl bound))
    {rootTheta : Nat → OrdinalDomain lambda} {rootEmbedding : Nat → RankElementaryEmbedding lambda}
    (root : RankFullMarkedRealization start rootTheta rootEmbedding) :
    WellFounded (fun (child parent : {a : Pattern // Generated a}) => Step parent.val child.val) := by
  have wf := rankTerminalDescent_wellFounded hl bounded
  have lift : ∀ a : Pattern, Acc (fun child parent => Step parent child) a →
      ∀ generated : Generated a,
        Acc (fun (child parent : {a : Pattern // Generated a}) => Step parent.val child.val) ⟨a, generated⟩ := by
    intro a accessible
    induction accessible with
    | intro a previous ih =>
      intro generated
      refine Acc.intro _ ?_
      intro child step
      exact ih child.val step child.property
  refine ⟨?_⟩
  intro a
  obtain ⟨theta, embedding, realization, _, _⟩ := rankFullMarkedRealization_generated hl root a.property
  exact lift a.val (rankFullMarkedRealization_accessible hl wf realization) a.property

end FullMarkedBLP
