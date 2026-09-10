import FullMarkedBLP.AuxiliaryRankRealization
import FullMarkedBLP.RankLinedWitness

namespace FullMarkedBLP

/-- Each initial segment of a fixed complete witness realizes exactly the
corresponding literal auxiliary expansion. The running terminal is recorded
as that witness's current point, and every old column remains unchanged. -/
theorem rankMarkedRealization_expandFrom_stages {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) {anchor k : Nat}
    (positive : 0 < anchor) (ha : anchor ≤ a.length) (size : 2 ≤ a.length)
    {right : OrdinalDomain lambda}
    (w : RankLinedWitness k (theta anchor) (theta (a.length + 1)) right)
    (i : Nat) (hi : i ≤ k) :
    ∃ (b : Pattern) (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      expandFrom anchor a i = some b ∧ RankMarkedRealization b newTheta newEmbedding ∧
      (∀ v, v ≤ a.length + 1 → newTheta v = theta v) ∧
      newTheta (b.length + 1) = w.point i ∧
      (0 < i → ∃ previousOwner, newEmbedding b.length = rankApply hl (w.factor (i - 1)) previousOwner) := by
  induction i with
  | zero =>
    exact ⟨a, theta, embedding, rfl, h, fun _ _ => rfl, w.start.symm, by omega⟩
  | succ i ih =>
    obtain ⟨previous, oldTheta, oldEmbedding, oldStep, oldRealization, oldColumns, oldTerminal, _⟩ :=
      ih (by omega)
    have length := (expandFrom_prefix oldStep).length_le
    have anchorBound : anchor ≤ previous.length := by omega
    have anchorEq : oldTheta anchor = theta anchor := oldColumns anchor (by omega)
    have critical : RankCriticalPoint (w.factor i) (oldTheta anchor) := by
      rw [anchorEq]
      exact w.criticalPoint i (by omega)
    have first : rankOrdinalAction (w.factor i) (oldTheta anchor) = oldTheta (previous.length + 1) := by
      rw [anchorEq, oldTerminal]
      exact w.firstEdge i (by omega)
    obtain ⟨b, step⟩ := auxiliaryStep_total oldRealization.valid positive anchorBound (by omega)
    obtain ⟨realization, columns, terminal, lastOwner⟩ :=
      rankMarkedRealization_auxiliaryStep hl oldRealization anchorBound (w.factor i) critical first step
    refine ⟨b, _, _, ?_, realization, ?_, ?_, ?_⟩
    · simp [expandFrom, oldStep, step]
    · intro v hv
      exact (columns v (by omega)).trans (oldColumns v hv)
    · exact terminal.trans (by rw [oldTerminal]; exact w.secondEdge i (by omega))
    · intro _
      exact ⟨oldEmbedding previous.length, by simpa using lastOwner⟩

/-- Using the entire k-step witness lands at its specified final endpoint.
The output owner is application of its last factor to the actual preceding
owner, on the original ambient rank domain. -/
theorem rankMarkedRealization_expandFrom_complete {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) {anchor k : Nat}
    (positive : 0 < anchor) (ha : anchor ≤ a.length) (size : 2 ≤ a.length)
    {right : OrdinalDomain lambda}
    (w : RankLinedWitness k (theta anchor) (theta (a.length + 1)) right) :
    ∃ (b : Pattern) (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      expandFrom anchor a k = some b ∧ RankMarkedRealization b newTheta newEmbedding ∧
      (∀ v, v ≤ a.length + 1 → newTheta v = theta v) ∧
      newTheta (b.length + 1) = right ∧
      ∃ previousOwner, newEmbedding b.length = rankApply hl (w.factor (k - 1)) previousOwner := by
  obtain ⟨b, newTheta, newEmbedding, step, realization, columns, terminal, lastOwner⟩ :=
    rankMarkedRealization_expandFrom_stages hl h positive ha size w k le_rfl
  exact ⟨b, newTheta, newEmbedding, step, realization, columns, terminal.trans w.finish,
    lastOwner w.positive⟩

end FullMarkedBLP

