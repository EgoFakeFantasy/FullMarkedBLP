import FullMarkedBLP.CopyRecordedFullPacket

namespace FullMarkedBLP

/-- Every factor of a successful current completion has exactly the terminal
packet width. Only strictly earlier events are assumed verified. -/
theorem shortCopy_completion_factor_widths {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    {sources word : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources) (computed : computeMarkTrace a r y = some word) :
    ∀ factor ∈ word.dropLast, ∃ ss, (factor, ss) ∈ rec ∧ ss.length = sources.length := by
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have records := scanRankReach_completion_all_factor_records reach entryReal currentReal
    (scanPriorVerifiedEvents_geometry verified) (scanPriorVerifiedEvents_endpoint_transport verified) hr hm hc word computed
  obtain ⟨other, terminal, otherComputed, atTerminal, record, _, _⟩ := completionRecord_iff.mp hc
  have same : other = word := Option.some.inj (otherComputed.symm.trans computed)
  subst other
  obtain ⟨front, last, shape⟩ := fromRight_two_decomposition atTerminal
  have lastFactor : word.dropLast.getLast? = some terminal := by rw [shape]; simp
  obtain ⟨_, _, _, _, _, _, _, _, trace⟩ := computeMarkTrace_sound hr hm computed
  have edges := trace_internal_predecessors trace
  apply list_all_of_last_and_backward (P := fun factor => ∃ ss, (factor, ss) ∈ rec ∧ ss.length = sources.length)
    lastFactor ⟨sources, recordAt_mem record, rfl⟩
  intro upper lower pair lowerWidth
  obtain ⟨lowerSources, lowerRecord, lowerWidth⟩ := lowerWidth
  obtain ⟨upperSources, upperRecord⟩ := records upper (List.of_mem_zip pair).1
  have pred := edges upper lower pair
  have width := (shortCopy_recorded_full_packet parentValid sat copy plain entryReal verified
    upperRecord lowerRecord (predecessor_lt currentReal.valid pred) pred).1
  exact ⟨upperSources, upperRecord, width.trans lowerWidth⟩

/-- Every target in the actual read packet has its complete parallel trace.
There is no current-event verification or extra packet-width assumption. -/
theorem shortCopy_completion_full_traces {lambda : Ordinal.{u}} {parent copied a : Pattern}
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
    ∃ word, computeMarkTrace a r y = some word ∧
      (∀ factor ∈ word.dropLast, ∃ ss, (factor, ss) ∈ rec ∧ ss.length = sources.length) ∧
      ∀ k, 0 < k → k ≤ sources.length →
        ∃ x ∈ sources, (sources.filter (· < x)).length = k - 1 ∧
          Trace a x (y + k) ((word.dropLast.map (fun i => i + k)) ++ [x]) := by
  obtain ⟨word, headSources, computed, headRecord, _, packet⟩ :=
    shortCopy_completion_head_packet parentValid sat copy reach entryReal currentReal verified hr hm hc
  have widths := shortCopy_completion_factor_widths parentValid sat copy reach entryReal currentReal verified hr hm hc computed
  obtain ⟨other, terminal, otherComputed, atTerminal, _, _, _⟩ := completionRecord_iff.mp hc
  have same : other = word := Option.some.inj (otherComputed.symm.trans computed)
  subst other
  obtain ⟨front, last, shape⟩ := fromRight_two_decomposition atTerminal
  obtain ⟨_, _, _, _, _, _, _, _, trace⟩ := computeMarkTrace_sound hr hm computed
  have head := trace_head trace
  have member : y ∈ word.dropLast := by
    cases front with
    | nil =>
      have eq : terminal = y := by simpa [shape] using head
      simp [shape, eq]
    | cons z rest =>
      have eq : z = y := by simpa [shape] using head
      have same : word = (y :: (rest ++ [terminal])) ++ [last] := by simp [shape, eq, List.append_assoc]
      rw [same, List.dropLast_concat]
      exact List.mem_cons_self
  obtain ⟨ss, ssRecord, width⟩ := widths y member
  have eq := scanReach_record_unique (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) ssRecord headRecord
  subst ss
  exact ⟨word, computed, widths, fun k hk hkt => packet k hk (by omega)⟩

end FullMarkedBLP
