import FullMarkedBLP.FullRankRealization

namespace FullMarkedBLP

/-- One actual application whose left operand has critical point below the
fixed bound. Arguments are child then parent, for well-founded recursion. -/
def RankBoundedApplication {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (bound : OrdinalDomain lambda) (child parent : RankElementaryEmbedding lambda) : Prop :=
  ∃ right critical, child = rankApply hl parent right ∧
    RankCriticalPoint parent critical ∧ critical < bound

/-- The precise descent supplied by a literal semantic step: either the
terminal decreases, or it stays fixed and the last owner descends by a
nonempty chain of actual applications below that same terminal. -/
def RankTerminalDescent {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (child parent : OrdinalDomain lambda × RankElementaryEmbedding lambda) : Prop :=
  child.1 < parent.1 ∨ (child.1 = parent.1 ∧
    Relation.TransGen (RankBoundedApplication hl parent.1) child.2 parent.2)

/-- The exact Step relation has full semantic lifts with bounded descent.
This local theorem uses real rank embeddings and the original syntax;
neither Steel nor I2 is a premise. -/
theorem rankFullMarkedRealization_step_bounded {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankFullMarkedRealization a theta embedding) (step : Step a b) :
    ∃ (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      RankFullMarkedRealization b newTheta newEmbedding ∧
      (∀ i, i ≤ 2 → newTheta i = theta i) ∧
      RankTerminalDescent hl (newTheta (b.length + 1), newEmbedding b.length)
        (theta (a.length + 1), embedding a.length) := by
  cases step with
  | cut success =>
    obtain ⟨result, terminal⟩ := rankFullMarkedRealization_cut h success
    exact ⟨theta, embedding, result, fun _ _ => rfl, Or.inl terminal⟩
  | expand positive success =>
    have kind : classify a = .successor ∨ classify a = .limit := by
      unfold expand at success
      split at success
      next kind => exact kind
      next => simp at success
    obtain ⟨out, newTheta, newEmbedding, computed, rows, lined, columns, terminal,
      factor, previousOwner, critical, lastOwner, cp, cb⟩ :=
      rankMarkedRealization_expand_total hl h.rows h.lined kind positive
    have same := Option.some.inj (computed.symm.trans success)
    subst out
    obtain ⟨_, _, _, _, _, _, size, _⟩ := rankMarkedRealization_expansion_edges h.rows kind
    obtain ⟨parentCritical, parentCp, parentBound⟩ :=
      rankRowRealization_last_critical (rankMarkedRealization_toRows h.rows) (by omega)
    refine ⟨newTheta, newEmbedding, ⟨rows, lined⟩, fun i hi => columns i (by omega), Or.inr ⟨terminal, ?_⟩⟩
    exact (Relation.TransGen.single (show RankBoundedApplication hl (theta (a.length + 1))
      (newEmbedding b.length) (rankApply hl (embedding a.length) factor) from
        ⟨previousOwner, critical, lastOwner, cp, cb⟩)).trans
      (Relation.TransGen.single ⟨factor, parentCritical, rfl, parentCp, parentBound⟩)
  | marked success =>
    obtain ⟨newTheta, newEmbedding, rows, columns, terminal, previousOwner, critical, lastOwner, cp, cb⟩ :=
      rankMarkedRealization_mStar_boundaries hl h.rows success
    have lined : RankAllFiniteLined (newTheta 0) (newTheta 1) (newTheta 2) := by
      simpa only [columns 0 (by omega), columns 1 (by omega), columns 2 (by omega)] using h.lined
    exact ⟨newTheta, newEmbedding, ⟨rows, lined⟩, columns,
      Or.inr ⟨terminal, Relation.TransGen.single ⟨previousOwner, critical, lastOwner, cp, cb⟩⟩⟩

end FullMarkedBLP
