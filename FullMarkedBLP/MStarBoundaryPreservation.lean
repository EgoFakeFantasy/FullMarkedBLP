import FullMarkedBLP.ScanBoundaryPreservation
import FullMarkedBLP.CopyBoundaryPreservation

namespace FullMarkedBLP

/-- Actual M_star totality with all semantic boundary data on its chosen
output realization. Scanning preserves the copy's final owner, hence the
whole operation is one bounded application from the parent's last owner. -/
theorem rankMarkedRealization_mStar_total_boundaries {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a copied : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding)
    (transient : classify a = .transient) (copy : shortCopy a = some copied) :
    ∃ (b : Pattern) (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      mStar a = some b ∧ RankMarkedRealization b newTheta newEmbedding ∧
      (∀ i, i ≤ 2 → newTheta i = theta i) ∧
      newTheta (b.length + 1) = theta (a.length + 1) ∧
      ∃ previousOwner critical,
        newEmbedding b.length = rankApply hl (embedding a.length) previousOwner ∧
        RankCriticalPoint (embedding a.length) critical ∧ critical < theta (a.length + 1) := by
  obtain ⟨last, p, e, lastAt, hp, he⟩ := shortCopy_parameters copy
  have rows := rankMarkedRealization_toRows h
  have entry := rankRowRealization_shortCopy hl rows copy lastAt hp he
  obtain ⟨copyColumns, copyTerminal, copyOwner⟩ :=
    rankRowRealization_shortCopy_boundaries hl rows copy lastAt hp he
  obtain ⟨b, newTheta, newEmbedding, scan, result, scanColumns, scanTerminal, scanOwner⟩ :=
    shortCopy_fullScan_total_preserves_boundaries hl h.valid h.sat copy entry
  obtain ⟨critical, cp, cb⟩ := rankRowRealization_last_critical rows (rowAt_bounds lastAt).1
  exact ⟨b, newTheta, newEmbedding,
    by simp only [mStar, transient, if_true, copy, Option.bind_some, scan], result,
    fun i hi => (scanColumns i hi).trans (copyColumns i hi), scanTerminal.trans copyTerminal,
    embedding (e - 1), critical, scanOwner.trans copyOwner, cp, cb⟩

/-- The same boundary package for any successful literal M_star edge. -/
theorem rankMarkedRealization_mStar_boundaries {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) (step : mStar a = some b) :
    ∃ (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      RankMarkedRealization b newTheta newEmbedding ∧
      (∀ i, i ≤ 2 → newTheta i = theta i) ∧
      newTheta (b.length + 1) = theta (a.length + 1) ∧
      ∃ previousOwner critical,
        newEmbedding b.length = rankApply hl (embedding a.length) previousOwner ∧
        RankCriticalPoint (embedding a.length) critical ∧ critical < theta (a.length + 1) := by
  unfold mStar at step
  split at step
  next transient =>
    obtain ⟨copied, copy, scan⟩ := Option.bind_eq_some_iff.mp step
    obtain ⟨out, newTheta, newEmbedding, step', result, columns, terminal, owner⟩ :=
      rankMarkedRealization_mStar_total_boundaries hl h transient copy
    have same : out = b := by
      have computed : mStar a = some b := by simp only [mStar, transient, if_true, copy, Option.bind_some, scan]
      exact Option.some.inj (step'.symm.trans computed)
    subst out
    exact ⟨newTheta, newEmbedding, result, columns, terminal, owner⟩
  next => simp at step

end FullMarkedBLP
