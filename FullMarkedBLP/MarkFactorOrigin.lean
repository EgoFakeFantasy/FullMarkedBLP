import FullMarkedBLP.HistoricalIndexOrigin

namespace FullMarkedBLP

/-- Actual original mark factors cannot be interior targets of recorded blocks. -/
theorem scanRankReach_mark_factor_origin {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entry : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (current : RankRowRealization a theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks) :
    ∃ word, MarkTrace a r y word ∧ computeMarkTrace a r y = some word ∧
      ∀ factor ∈ word.dropLast, 0 < factor →
        (∃ ss, (factor, ss) ∈ rec) ∨
        (∃ before after history, ScanReach initial before history factor ∧
          native (completeFrozenMarks before history factor) factor = some (after, []) ∧
          rowAt a factor = rowAt after factor) := by
  obtain ⟨phi, mono, _, aligned, certs⟩ :=
    scanRankReach_current_historical_certificates reach entry geometry hr
  obtain ⟨xs, delta, marked, computed, _, _⟩ := certs y hm
  refine ⟨xs.map phi, marked, computed, ?_⟩
  intro factor mem positive
  have inWord := (List.dropLast_sublist (xs.map phi)).subset mem
  obtain ⟨j, _, eq⟩ := List.mem_map.mp inWord
  obtain ⟨_, _, source, _, _, _, _, _, trace⟩ := marked
  have bound := trace_member_le_head current.valid trace
    ((List.dropLast_sublist (xs.map phi)).subset mem)
  have ownerBound := ((current.proper r row hr).2 y hm).1
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have result := scanReach_historical_image_origin plain mono aligned
    (j := j) (by simpa only [eq] using positive) (by omega)
  simpa only [eq] using result

end FullMarkedBLP
