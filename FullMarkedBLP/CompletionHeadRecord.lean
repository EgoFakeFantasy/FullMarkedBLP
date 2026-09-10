import FullMarkedBLP.CompletionFactorRecords

namespace FullMarkedBLP

/-- The head, as well as every internal factor, has a retained record whenever
an entrance completion succeeds. -/
theorem scanRankReach_completion_head_record {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    {sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization initial initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (transport : ScanPriorEndpointTransport initial initialTheta initialEmbedding r)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources) :
    ∃ ss, (y, ss) ∈ rec := by
  obtain ⟨xs, terminal, computed, terminalAt, _, _, _⟩ := completionRecord_iff.mp hc
  obtain ⟨_, _, _, _, _, _, _, _, trace⟩ := computeMarkTrace_sound hr hm computed
  have head := trace_head trace
  have mem : y ∈ xs.dropLast := by
    obtain ⟨front, last, shape⟩ := fromRight_two_decomposition terminalAt
    cases front with
    | nil =>
      have eq : terminal = y := by simpa [shape] using head
      simp [shape, eq]
    | cons z rest =>
      have eq : z = y := by simpa [shape] using head
      have same : xs = (y :: (rest ++ [terminal])) ++ [last] := by
        simp [shape, eq, List.append_assoc]
      rw [same, List.dropLast_concat]
      exact List.mem_cons_self
  exact scanRankReach_completion_all_factor_records reach entryReal currentReal geometry transport hr hm hc
    xs computed y mem

end FullMarkedBLP

