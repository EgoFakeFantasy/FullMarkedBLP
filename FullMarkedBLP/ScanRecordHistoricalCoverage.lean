import FullMarkedBLP.ScanRankReach

namespace FullMarkedBLP

/-- The retained terminal packet is strictly covered by its actual birth
successor. Realization of native entrances remains an explicit local obligation. -/
theorem scanRankReach_record_historical_coverage {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entrances : ∀ before history owner oldTheta oldEmbedding,
      ScanRankReach initial initialTheta initialEmbedding before history owner oldTheta oldEmbedding → owner < r →
      RankRowRealization (completeFrozenMarks before history owner) oldTheta oldEmbedding)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) :
    ∃ before history oldTheta oldEmbedding after,
      ScanRankReach initial initialTheta initialEmbedding before history terminal oldTheta oldEmbedding ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) ∧
      ∀ k, k < sources.length → (theta (terminal + 1 + k)).val < (oldTheta (terminal + 1)).val := by
  obtain ⟨before, history, oldTheta, oldEmbedding, after, reach, hn, _, _, targets⟩ :=
    scanRankReach_record_birth h hm
  have hreal := entrances before history terminal oldTheta oldEmbedding reach
    ((scanReach_records_before (scanEmbeddingReach_forget (scanRankReach_embeddings h))).2
      (terminal, sources) hm).2.1
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  have hv := hreal.valid terminal row hr
  have hl := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
  refine ⟨before, history, oldTheta, oldEmbedding, after, reach, hn, ?_⟩
  intro k hk
  rw [targets k hk]
  exact rankRealization_native_fresh_upper hreal hr hp he (native_sources_of_success hn) k

end FullMarkedBLP


