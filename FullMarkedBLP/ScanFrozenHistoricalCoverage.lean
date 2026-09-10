import FullMarkedBLP.ScanFrozenHistoricalCertificates
import FullMarkedBLP.ScanEntryPacketCoverage

namespace FullMarkedBLP

/-- Historical marked words and record packet coverage share one origin map. -/
theorem scanRankReach_frozen_historical_coverage {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j)
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
        ∃ i, phi i = terminal ∧ phi (i + 1) = terminal + sources.length + 1 ∧
          ∀ front delta,
            naturalCutoff (fun v => rankOrdinalAction (initialEmbedding v)) initialTheta
              (front ++ [i]) = some delta →
            ∀ k, k < sources.length →
              evalWord (fun v => rankOrdinalAction (embedding v)) (front.map phi)
                (theta (terminal + 1 + k)) < delta) ∧
      ∀ y ∈ current.marks, ∃ (xs : List Nat) (delta : OrdinalDomain lambda),
        MarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y (xs.map phi) ∧
        computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some (xs.map phi) ∧
        naturalCutoff (fun i => rankOrdinalAction (initialEmbedding i)) initialTheta xs.dropLast = some delta ∧
        rankCutoffAgreement delta.val (embedding r)
          (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) (xs.dropLast.map phi)) := by
  obtain ⟨phi, mono, holds, records, certs⟩ :=
    scanRankReach_frozen_historical_certificates h entryRealization geometry processed events valid hr
  refine ⟨phi, mono, holds, ?_, certs⟩
  intro terminal sources record
  obtain ⟨i, hi, next⟩ := records terminal sources record
  refine ⟨i, hi, next, ?_⟩
  intro front delta cutoff k hk
  have bound := scanReach_record_targets_before
    (scanEmbeddingReach_forget (scanRankReach_embeddings h)) record
  have rb := rowAt_bounds hr
  have target : theta (terminal + 1 + k) < initialTheta (i + 1) := by
    rw [← (holds (i + 1)).1, next]
    exact increasing _ _ (by omega) (by omega)
  rw [evalWord_reindex
    (fun v => rankOrdinalAction (initialEmbedding v))
    (fun v => rankOrdinalAction (embedding v)) phi front
    (fun v _ => by dsimp only; rw [(holds v).2])]
  exact terminal_packet_below_natural_cutoff initialEmbedding initialTheta front i target cutoff

end FullMarkedBLP
