import FullMarkedBLP.ScanHistoricalWidthCutoff
import FullMarkedBLP.FrozenHistoricalTrace

namespace FullMarkedBLP

/-- Arbitrary original marked words retain their entry cutoff and same-map record alignment at intermediate frozen states. -/
theorem scanRankReach_frozen_bounded_historical_certificates {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (valid : ∀ i rw,
      rowAt (processed.foldl (fun current z => completeMark current rec r z) a) i = some rw → rw.CoreValid i)
    {current : Row} (hr : rowAt a r = some current) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, phi i = terminal ∧ phi (i + 1) = terminal + sources.length + 1) ∧
      ∀ y ∈ current.marks, ∃ (xs : List Nat) (delta : OrdinalDomain lambda),
        MarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y (xs.map phi) ∧
        computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some (xs.map phi) ∧
        naturalCutoff (fun i => rankOrdinalAction (initialEmbedding i)) initialTheta xs.dropLast = some delta ∧
        (∀ ss, (y, ss) ∈ rec → delta ≤ theta (y + ss.length + 1)) ∧
        rankCutoffAgreement delta.val (embedding r)
          (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) (xs.dropLast.map phi)) := by
  obtain ⟨phi, mono, holds, records, certs⟩ :=
    scanRankReach_current_bounded_historical_certificates h entryRealization geometry hr
  refine ⟨phi, mono, holds, records, ?_⟩
  intro y hy
  obtain ⟨xs, delta, trace, _, cutoff, bound, saved⟩ := certs y hy
  have transported := frozen_fold_preserves_historical_trace processed events trace
  exact ⟨xs, delta, transported, computeMarkTrace_complete valid transported, cutoff, bound, saved⟩

end FullMarkedBLP

