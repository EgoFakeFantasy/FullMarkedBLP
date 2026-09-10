import FullMarkedBLP.ScanOriginAlignment

namespace FullMarkedBLP

/-- Actual record targets, propagated through mapped entry factors, are
strictly covered by the original natural cutoff. Only current column
monotonicity is needed; prior entrance realizations are not assumed. -/
theorem scanRankReach_entry_packet_coverage {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      ∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, 1 ≤ i ∧ i ≤ initial.length ∧ phi i = terminal ∧
          phi (i + 1) = terminal + sources.length + 1 ∧
          ∀ front delta,
            naturalCutoff (fun v => rankOrdinalAction (initialEmbedding v)) initialTheta
              (front ++ [i]) = some delta →
            ∀ k, k < sources.length →
              evalWord (fun v => rankOrdinalAction (embedding v)) (front.map phi)
                (theta (terminal + 1 + k)) < delta := by
  obtain ⟨phi, original, hmono, hzero, _, hmax, hlen, holds, _, _, records⟩ :=
    scanRankReach_origin_alignment h
  refine ⟨phi, hmono, hzero, holds, ?_⟩
  intro terminal sources hm
  obtain ⟨i, hi, hib, he, hnext⟩ := records terminal sources hm
  have hb := scanReach_record_targets_before
    (scanEmbeddingReach_forget (scanRankReach_embeddings h)) hm
  refine ⟨i, hi, by omega, he, hnext, ?_⟩
  intro front delta hd k hk
  have ht : theta (terminal + 1 + k) < initialTheta (i + 1) := by
    rw [← (holds (i + 1)).1, hnext]
    exact increasing _ _ (by omega) (by omega)
  rw [evalWord_reindex
    (fun v => rankOrdinalAction (initialEmbedding v))
    (fun v => rankOrdinalAction (embedding v)) phi front
    (fun v _ => by dsimp only; rw [(holds v).2])]
  exact terminal_packet_below_natural_cutoff initialEmbedding initialTheta front i ht hd

end FullMarkedBLP

