import FullMarkedBLP.ScanCurrentMarkOrigins

namespace FullMarkedBLP

/-- No original column of the current row lies inside a recorded insertion
block. Any later full-row entry lies strictly beyond all its targets. -/
theorem scanRankReach_current_record_gap {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y target : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    {row : Row} {sources : List Nat} (hr : rowAt a r = some row)
    (hm : (y, sources) ∈ rec) (ht : target ∈ row.full r) (hlt : y < target) :
    y + sources.length < target := by
  obtain ⟨phi, original, entry, hmono, _, _, _, shape, _, records, _, _⟩ :=
    scanRankReach_current_mark_origins h hr
  obtain ⟨i, _, hi, hn⟩ := records y sources hm
  change target ∈ row.core ++ [r + 1] at ht
  rcases List.mem_append.mp ht with hc | hend
  · rw [shape] at hc
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hc
    have hij : i < j := by
      by_contra hh
      have le := hmono.monotone (by omega : j ≤ i)
      rw [hi, hj] at le
      omega
    have le := hmono.monotone (by omega : i + 1 ≤ j)
    rw [hn, hj] at le
    omega
  · have he : target = r + 1 := by simpa using hend
    have bound := scanReach_record_targets_before (scanEmbeddingReach_forget (scanRankReach_embeddings h)) hm
    omega

end FullMarkedBLP
