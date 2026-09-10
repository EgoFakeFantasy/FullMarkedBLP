import FullMarkedBLP.CopyNativeFullPacket

namespace FullMarkedBLP

/-- Adjacent retained factors inherit their whole equal-width packet
from the original Sat short-copy birth, without a source-entry hypothesis. -/
theorem shortCopy_recorded_full_packet {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r upper lower : Nat}
    {upperSources lowerSources : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanReach copied a rec r)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    (upperRecord : (upper, upperSources) ∈ rec) (lowerRecord : (lower, lowerSources) ∈ rec)
    (lowerUpper : lower < upper) (pred : predecessor a upper = some lower) :
    upperSources.length = lowerSources.length ∧ ∀ k, 0 < k → k ≤ upperSources.length →
      lower + k ∈ upperSources ∧ predecessor a (upper + k) = some (lower + k) := by
  obtain ⟨before, after, history, oldReach, lowerAtBirth, birth, unchanged⟩ :=
    scanReach_ordered_record_birth reach upperRecord lowerRecord lowerUpper
  have upperBefore := scanReach_record_targets_before reach upperRecord
  obtain ⟨theta, embedding, labelled⟩ := scanReach_rank_lift oldReach initialTheta initialEmbedding
  obtain ⟨h, events⟩ := verified before history upper theta embedding labelled (by omega)
  have prior : ScanPriorVerifiedEvents copied initialTheta initialEmbedding upper := by
    intro state history owner values embeddings reached earlier
    exact verified state history owner values embeddings reached (by omega)
  obtain ⟨mid, atMid, _⟩ := Option.bind_eq_some_iff.mp birth
  have rb := rowAt_bounds atMid
  obtain ⟨row, hr⟩ := rowAt_exists (a := before) rb.1 (by simpa only [completeFrozenMarks_length] using rb.2)
  obtain ⟨valid, fixed⟩ := completeFrozenMarks_event_geometry hr h.valid (events row hr)
  have room := Row.step_lt_length (valid upper mid atMid).2.2.2
  obtain ⟨p, atP⟩ := fromRight_exists (xs := mid.core) (k := mid.step + 1) (by omega) (by omega)
  have midP : predecessor (completeFrozenMarks before history upper) upper = some p := by
    simp only [predecessor, atMid, Option.bind_some]
    exact atP
  have afterP := native_owner_predecessor valid birth midP
  have currentP : predecessor a upper = some p := by
    simpa only [predecessor, unchanged upper (by omega)] using afterP
  have same : p = lower := Option.some.inj (currentP.symm.trans pred)
  subst p
  have oldP : row.p = some lower := by
    rw [fixed] at midP
    simpa only [predecessor, hr, Option.bind_some] using midP
  have room := Row.step_lt_length (h.valid upper row hr).2.2.2
  obtain ⟨e, atE⟩ := fromRight_exists (xs := row.core) (k := row.step)
    (h.valid upper row hr).2.2.2.1 (by omega)
  have nonempty := ((scanReach_records_before reach).2 (upper, upperSources) upperRecord).2.2
  obtain ⟨width, packet⟩ := shortCopy_native_birth_full_packet parentValid sat copy labelled entryReal h prior
    hr oldP atE lowerAtBirth (events row hr) birth nonempty
  refine ⟨width, ?_⟩
  intro k hk hkt
  obtain ⟨member, edge⟩ := packet k hk (by omega)
  exact ⟨member, by simpa only [predecessor, unchanged (upper + k) (by omega)] using edge⟩

end FullMarkedBLP

