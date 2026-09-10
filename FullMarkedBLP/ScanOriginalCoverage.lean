import FullMarkedBLP.ScanOriginalTail
import FullMarkedBLP.ScanRecordHistoricalCoverage

namespace FullMarkedBLP

/-- Terminal target coverage by a located successor in the original scan
sequence, using only strictly prior native entrance realizations. -/
theorem scanRankReach_record_original_coverage {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entrances : ∀ before history owner oldTheta oldEmbedding,
      ScanRankReach initial initialTheta initialEmbedding before history owner oldTheta oldEmbedding →
      owner < r → RankRowRealization (completeFrozenMarks before history owner) oldTheta oldEmbedding)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) :
    ∃ original, 1 ≤ original ∧ original ≤ initial.length ∧
      ∀ k, k < sources.length → theta (terminal + 1 + k) < initialTheta (original + 1) := by
  obtain ⟨before, history, oldTheta, oldEmbedding, after, reach, hn, covered⟩ :=
    scanRankReach_record_historical_coverage h entrances hm
  obtain ⟨original, hp, hmax, hlen, tail⟩ := scanRankReach_original_tail reach
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  have hbound := (rowAt_bounds hr).2
  rw [completeFrozenMarks_length] at hbound
  refine ⟨original, hp, by omega, ?_⟩
  intro k hk
  have ht : theta (terminal + 1 + k) < oldTheta (terminal + 1) := covered k hk
  rwa [(tail 1).1] at ht

end FullMarkedBLP
