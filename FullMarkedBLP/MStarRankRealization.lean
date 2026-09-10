import FullMarkedBLP.CopyRankRealization
import FullMarkedBLP.CopyFullScanClosure

namespace FullMarkedBLP

/-- The copied-entry realization premise of full-scan closure is discharged
from the parent certificate and actual short-copy success. -/
theorem rankMarkedRealization_copy_fullScan {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a copied : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankMarkedRealization a theta embedding)
    (copy : shortCopy a = some copied) :
    ∃ (b : Pattern) (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      fullScan copied = some b ∧ RankMarkedRealization b newTheta newEmbedding := by
  obtain ⟨entryTheta, entryEmbedding, entry⟩ := shortCopy_has_rankRealization hl (rankMarkedRealization_toRows h) copy
  exact shortCopy_fullScan_total_realized hl h.valid h.sat copy entry

/-- Every legally copyable transient parent has an actual M_star output
with all row edges, critical points, natural marked certificates and Sat.
The ambient rank domain is unchanged. First-triple linedness is separate. -/
theorem rankMarkedRealization_mStar_total {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a copied : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankMarkedRealization a theta embedding)
    (transient : classify a = .transient) (copy : shortCopy a = some copied) :
    ∃ (b : Pattern) (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      mStar a = some b ∧ RankMarkedRealization b newTheta newEmbedding := by
  obtain ⟨b, newTheta, newEmbedding, scan, result⟩ := rankMarkedRealization_copy_fullScan hl h copy
  exact ⟨b, newTheta, newEmbedding, by simp only [mStar, transient, if_true, copy, Option.bind_some, scan], result⟩

theorem rankMarkedRealization_mStar {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankMarkedRealization a theta embedding)
    (step : mStar a = some b) :
    ∃ (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      RankMarkedRealization b newTheta newEmbedding := by
  unfold mStar at step
  split at step
  next transient =>
    obtain ⟨copied, copy, scan⟩ := Option.bind_eq_some_iff.mp step
    obtain ⟨out, newTheta, newEmbedding, scan', result⟩ := rankMarkedRealization_copy_fullScan hl h copy
    have same := Option.some.inj (scan'.symm.trans scan)
    subst out
    exact ⟨newTheta, newEmbedding, result⟩
  next => simp at step

/-- On realized transient parents, scanning introduces no extra failure
condition beyond the original partial short-copy legality. -/
theorem mStar_exists_iff_shortCopy {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankMarkedRealization a theta embedding)
    (transient : classify a = .transient) :
    (∃ b, mStar a = some b) ↔ ∃ copied, shortCopy a = some copied := by
  constructor
  · rintro ⟨b, step⟩
    simp only [mStar, transient, if_true] at step
    obtain ⟨copied, copy, _⟩ := Option.bind_eq_some_iff.mp step
    exact ⟨copied, copy⟩
  · rintro ⟨copied, copy⟩
    obtain ⟨b, _, _, step, _⟩ := rankMarkedRealization_mStar_total hl h transient copy
    exact ⟨b, step⟩

end FullMarkedBLP
