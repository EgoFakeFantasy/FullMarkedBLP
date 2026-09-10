import FullMarkedBLP.ScanOriginAlignment

namespace FullMarkedBLP

/-- Every position within a recorded block has the original factor embedding;
its successor lies at or below the corresponding original successor column. -/
theorem scanRankReach_parallel_factor_bounds {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      ∀ v sources, (phi v, sources) ∈ rec → ∀ offset, offset ≤ sources.length →
        embedding (phi v + offset) = initialEmbedding v ∧
        theta (phi v + offset + 1) ≤ initialTheta (v + 1) := by
  obtain ⟨phi, original, hmono, hzero, _, hmax, hlen, holds, _, _, records⟩ :=
    scanRankReach_origin_alignment h
  refine ⟨phi, hmono, hzero, holds, ?_⟩
  intro v sources hm offset hoff
  obtain ⟨i, hi, hib, he, hnext⟩ := records (phi v) sources hm
  have hiv := hmono.injective he
  subst i
  have bound := scanReach_record_targets_before
    (scanEmbeddingReach_forget (scanRankReach_embeddings h)) hm
  constructor
  · rw [scanEmbeddingReach_records_agree (scanRankReach_embeddings h) (phi v) sources hm offset hoff]
    exact (holds v).2
  · rw [← (holds (v + 1)).1, hnext]
    by_cases heq : offset = sources.length
    · simp [heq]
    · exact (increasing _ _ (by omega) (by omega)).le

/-- Parallel words inherit entry weak agreement at their own natural cutoff.
The required block incidences still need to come from the actual packet theorem. -/
theorem scanRankReach_parallel_word_certificates {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      ∀ word offset (owner : RankElementaryEmbedding lambda) (delta : OrdinalDomain lambda),
        naturalCutoff (fun v => rankOrdinalAction (initialEmbedding v)) initialTheta word = some delta →
        rankCutoffAgreement delta.val owner
          (evalWord (fun v => (initialEmbedding v : RankDomain lambda → RankDomain lambda)) word) →
        (∀ v ∈ word, ∃ sources, (phi v, sources) ∈ rec ∧ offset ≤ sources.length) →
        ∃ newDelta, newDelta ≤ delta ∧
          naturalCutoff (fun v => rankOrdinalAction (embedding v)) theta
            (word.map (fun v => phi v + offset)) = some newDelta ∧
          rankCutoffAgreement newDelta.val owner
            (evalWord (fun v => (embedding v : RankDomain lambda → RankDomain lambda))
              (word.map (fun v => phi v + offset))) := by
  obtain ⟨phi, hmono, hzero, holds, block⟩ := scanRankReach_parallel_factor_bounds h increasing
  refine ⟨phi, hmono, hzero, holds, ?_⟩
  intro word offset owner delta hd hc blocks
  have factors : ∀ v ∈ word, embedding (phi v + offset) = initialEmbedding v := by
    intro v hv
    obtain ⟨sources, hm, hb⟩ := blocks v hv
    exact (block v sources hm offset hb).1
  have successors : ∀ v ∈ word, theta (phi v + offset + 1) ≤ initialTheta (v + 1) := by
    intro v hv
    obtain ⟨sources, hm, hb⟩ := blocks v hv
    exact (block v sources hm offset hb).2
  have hn : word ≠ [] := by intro he; subst word; simp [naturalCutoff] at hd
  obtain ⟨newDelta, hnew⟩ := naturalCutoff_defined (fun v => rankOrdinalAction (embedding v)) theta
    (by simpa using hn : word.map (fun v => phi v + offset) ≠ [])
  refine ⟨newDelta, ?_, hnew, ?_⟩
  · exact naturalCutoff_reindex_le _ _ initialTheta theta (fun v => phi v + offset) word
      (fun v => rankOrdinalAction_monotone (initialEmbedding v))
      (fun v hv => congrArg rankOrdinalAction (factors v hv)) successors hd hnew
  · exact rankCertificate_reindex initialEmbedding embedding initialTheta theta
      (fun v => phi v + offset) word owner factors successors hd hnew hc

end FullMarkedBLP
