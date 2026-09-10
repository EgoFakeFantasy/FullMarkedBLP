import FullMarkedBLP.CopyTraceThroughHead
import FullMarkedBLP.CompletionFactorRecords

namespace FullMarkedBLP

/-- An actual successful completion has complete parallel traces through its
head-record width. The terminal packet may still be wider; ruling that out is
separate from this theorem and is not assumed in this statement. -/
theorem shortCopy_completion_head_packet {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    {sources : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources) :
    ∃ word headSources, computeMarkTrace a r y = some word ∧ (y, headSources) ∈ rec ∧
      headSources.length ≤ sources.length ∧
      ∀ k, 0 < k → k ≤ headSources.length →
        ∃ x ∈ sources, (sources.filter (· < x)).length = k - 1 ∧
          Trace a x (y + k) ((word.dropLast.map (fun i => i + k)) ++ [x]) := by
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  obtain ⟨word, terminal, computed, terminalAt, recorded, _, _⟩ := completionRecord_iff.mp hc
  obtain ⟨_, _, _, _, _, _, _, _, trace⟩ := computeMarkTrace_sound hr hm computed
  have records := scanRankReach_completion_all_factor_records reach entryReal currentReal
    (scanPriorVerifiedEvents_geometry verified) (scanPriorVerifiedEvents_endpoint_transport verified) hr hm hc
    word computed
  obtain ⟨front, last, shape⟩ := fromRight_two_decomposition terminalAt
  have head := trace_head trace
  have factors : ∃ tail, word.dropLast = y :: tail := by
    cases front with
    | nil =>
      have eq : terminal = y := by simpa [shape] using head
      exact ⟨[], by simp [shape, eq]⟩
    | cons z rest =>
      have eq : z = y := by simpa [shape] using head
      have same : word = (y :: (rest ++ [terminal])) ++ [last] := by simp [shape, eq, List.append_assoc]
      exact ⟨rest ++ [terminal], by rw [same, List.dropLast_concat]⟩
  obtain ⟨tail, factors⟩ := factors
  obtain ⟨headSources, headRecord⟩ := records y (by rw [factors]; exact List.mem_cons_self)
  have lastFactor : (y :: tail).getLast? = some terminal := by rw [← factors, shape]; simp
  have member := recordAt_mem recorded
  have sizes := (shortCopy_recorded_parallel_through_head parentValid sat copy plain entryReal verified
    currentReal.valid trace factors headRecord records).1
  obtain ⟨ss, ssRecord, width⟩ := sizes terminal (by rw [factors]; exact List.mem_of_getLast? lastFactor)
  have same := scanReach_record_unique plain ssRecord member
  subst ss
  refine ⟨word, headSources, computed, headRecord, width, ?_⟩
  intro k hk hkt
  exact shortCopy_recorded_trace_through_head parentValid sat copy plain entryReal verified currentReal.valid
    trace factors headRecord records lastFactor member hk hkt

end FullMarkedBLP
