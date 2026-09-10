import FullMarkedBLP.CopyScanRealization

namespace FullMarkedBLP

/-- The literal full scan of a realized Sat short copy succeeds and has a
saturated marked row realization. This includes all natural-cutoff mark
certificates; FullRankRealization also transports first-triple linedness. -/
theorem shortCopy_fullScan_total_realized {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {parent copied : Pattern} {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding) :
    ∃ (b : Pattern) (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda),
      fullScan copied = some b ∧ RankMarkedRealization b theta embedding := by
  have historyValid : ∀ before history owner, ScanReach copied before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i := by
    intro before history owner prior
    obtain ⟨theta, embedding, labelled⟩ := scanReach_rank_lift prior initialTheta initialEmbedding
    have result := shortCopy_scan_realization hl parentValid sat copy entryReal labelled
    cases hr : rowAt before owner with
    | none => simpa only [completeFrozenMarks, hr] using result.1.valid
    | some row => exact (result.2 row hr).1.valid
  obtain ⟨b, success, saturated⟩ := fullScan_total_sat_of_history_valid historyValid
  obtain ⟨rec, cursor, reach, _, _⟩ := fullScan_reaches_end success
  obtain ⟨theta, embedding, labelled⟩ := scanReach_rank_lift reach initialTheta initialEmbedding
  have result := shortCopy_scan_realization hl parentValid sat copy entryReal labelled
  exact ⟨b, theta, embedding, success, rankRowRealization_with_sat result.1 saturated⟩

end FullMarkedBLP
