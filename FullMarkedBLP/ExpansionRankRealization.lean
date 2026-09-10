import FullMarkedBLP.ExpansionRankEdges

namespace FullMarkedBLP

/-- A complete first-triple witness constructs the actual E(k) realization.
The old terminal is recovered at the full length k; the last owner is two
applications from the parent's last owner, with the intermediate critical
point strictly below that common terminal. -/
theorem rankMarkedRealization_expand {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding)
    (kind : classify a = .successor ∨ classify a = .limit) {k : Nat}
    (w : RankLinedWitness k (theta 0) (theta 1) (theta 2)) :
    ∃ (b : Pattern) (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      expand a k = some b ∧ RankMarkedRealization b newTheta newEmbedding ∧
      (∀ v, v ≤ a.length → newTheta v = theta v) ∧
      newTheta (b.length + 1) = theta (a.length + 1) ∧
      ∃ previousOwner critical,
        newEmbedding b.length = rankApply hl (rankApply hl (embedding a.length) (w.factor (k - 1))) previousOwner ∧
        RankCriticalPoint (rankApply hl (embedding a.length) (w.factor (k - 1))) critical ∧
        critical < theta (a.length + 1) := by
  obtain ⟨row, anchor, lastGet, hb, positive, bound, size, image0, image1, image2⟩ :=
    rankMarkedRealization_expansion_edges h kind
  have cutStep : cut a = some a.dropLast := by simp [cut, size]
  have cutLength : a.dropLast.length + 1 = a.length := by simp; omega
  let transported := w.apply hl (embedding a.length)
  let mapped : RankLinedWitness k (theta anchor) (theta (a.dropLast.length + 1)) (theta (a.length + 1)) := {
    point := transported.point
    factor := transported.factor
    positive := w.positive
    critical_lt := by
      rw [cutLength, ← image0, ← image1]
      exact transported.critical_lt
    start := transported.start.trans (by rw [cutLength]; exact image1)
    finish := transported.finish.trans image2
    increasing := transported.increasing
    criticalPoint := by intro i hi; rw [← image0]; exact transported.criticalPoint i hi
    firstEdge := by intro i hi; rw [← image0]; exact transported.firstEdge i hi
    secondEdge := transported.secondEdge }
  obtain ⟨b, newTheta, newEmbedding, step, realization, columns, terminal, previousOwner, lastOwner⟩ :=
    rankMarkedRealization_expandFrom_complete hl (rankMarkedRealization_cut h cutStep)
      positive (by simpa using bound) (by simp; omega) mapped
  refine ⟨b, newTheta, newEmbedding, ?_, realization, ?_, terminal, previousOwner, theta anchor, ?_, ?_, ?_⟩
  · simp [expand, kind, lastGet, hb, cutStep, step]
  · intro v hv
    exact columns v (by omega)
  · exact lastOwner
  · change RankCriticalPoint (transported.factor (k - 1)) (theta anchor)
    rw [← image0]
    exact transported.criticalPoint (k - 1) (by have := w.positive; omega)
  · exact h.increasing anchor (a.length + 1) (by omega) le_rfl

/-- With the manuscript's whole common-endpoint finite witness family,
every positive literal E parameter succeeds. The entire family remains
available at the unchanged first triple for all future parameters. -/
theorem rankMarkedRealization_expand_total {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding)
    (lined : RankAllFiniteLined (theta 0) (theta 1) (theta 2))
    (kind : classify a = .successor ∨ classify a = .limit) {k : Nat} (positive : 0 < k) :
    ∃ (b : Pattern) (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      expand a k = some b ∧ RankMarkedRealization b newTheta newEmbedding ∧
      RankAllFiniteLined (newTheta 0) (newTheta 1) (newTheta 2) ∧
      (∀ v, v ≤ a.length → newTheta v = theta v) ∧
      newTheta (b.length + 1) = theta (a.length + 1) ∧
      ∃ factor previousOwner critical,
        newEmbedding b.length = rankApply hl (rankApply hl (embedding a.length) factor) previousOwner ∧
        RankCriticalPoint (rankApply hl (embedding a.length) factor) critical ∧
        critical < theta (a.length + 1) := by
  obtain ⟨w⟩ := lined k positive
  obtain ⟨b, newTheta, newEmbedding, step, realization, columns, terminal, previousOwner, critical, lastOwner, cp, cb⟩ :=
    rankMarkedRealization_expand hl h kind w
  obtain ⟨_, _, _, _, _, _, size, _⟩ := rankMarkedRealization_expansion_edges h kind
  refine ⟨b, newTheta, newEmbedding, step, realization, ?_, columns, terminal,
    w.factor (k - 1), previousOwner, critical, lastOwner, cp, cb⟩
  simpa only [columns 0 (by omega), columns 1 (by omega), columns 2 (by omega)] using lined

end FullMarkedBLP
