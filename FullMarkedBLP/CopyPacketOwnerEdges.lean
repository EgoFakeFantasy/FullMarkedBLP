import FullMarkedBLP.CopyFrozenFullTraces

namespace FullMarkedBLP

/-- Literal parallel traces evaluate using the original factor embeddings. -/
theorem recorded_parallel_trace_image {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {word : List Nat} {x y k : Nat}
    (h : RankRowRealization a theta embedding) (agree : RecordedEmbeddingsAgree embedding rec)
    (records : ∀ factor ∈ word, ∃ ss, (factor, ss) ∈ rec ∧ k ≤ ss.length)
    (trace : Trace a x (y + k) (word.map (fun i => i + k) ++ [x])) :
    evalWord (fun i => rankOrdinalAction (embedding i)) word (theta x) = theta (y + k) := by
  have result := realized_trace_word_image (fun i => rankOrdinalAction (embedding i)) theta h.valid h.edges trace
  rw [List.dropLast_concat] at result
  have reindex := evalWord_reindex (fun i => rankOrdinalAction (embedding i))
    (fun i => rankOrdinalAction (embedding i)) (fun i => i + k) word (by
      intro i hi
      obtain ⟨ss, member, width⟩ := records i hi
      dsimp only
      rw [agree i ss member k width]) (theta x)
  exact reindex.symm.trans result

/-- Every actual source of a successful frozen completion has the required
owner edge. Only earlier scan events and earlier marks are verified; the
current event's packet correctness is the conclusion. -/
theorem shortCopy_frozen_completion_packet_edges {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    {sources : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (midReal : RankRowRealization
      (processed.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length) := by
  have geometry := scanPriorVerifiedEvents_geometry verified
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have agree := scanEmbeddingReach_records_agree (scanRankReach_embeddings reach)
  obtain ⟨word, computed, widths, traces⟩ := shortCopy_frozen_completion_full_traces parentValid sat copy reach
    entryReal currentReal verified processed events hr hm hc
  obtain ⟨front, terminal, last, wordComputed, record, ownerEdges⟩ :=
    scanRankReach_frozen_recorded_owner_edges reach entryReal geometry currentReal.increasing processed events
      midReal.valid hr hm hc
  have shape : word = front ++ [terminal, last] := Option.some.inj (computed.symm.trans wordComputed)
  have member := recordAt_mem record
  have bounds := scanRankReach_record_source_bounds reach
    (fun before history owner oldTheta oldEmbedding reached earlier =>
      (geometry before history owner oldTheta oldEmbedding reached earlier).1) member
  have historyValid : ∀ before history owner, ScanReach copied before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i := by
    intro before history owner reached earlier
    obtain ⟨oldTheta, oldEmbedding, labelled⟩ := scanReach_rank_lift reached initialTheta initialEmbedding
    exact (geometry before history owner oldTheta oldEmbedding labelled earlier).1
  intro x hx
  have rankBound : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  obtain ⟨other, otherMember, otherRank, trace⟩ := traces
    ((sources.filter (· < x)).length + 1) (by omega) (by omega)
  have rankEq : (sources.filter (· < other)).length = (sources.filter (· < x)).length := by
    simpa only [Nat.add_sub_cancel] using otherRank
  have firstEdge := scanReach_record_predecessor_prior plain historyValid member hx
  have otherEdge := scanReach_record_predecessor_prior plain historyValid member otherMember
  rw [rankEq] at otherEdge
  have same : other = x := Option.some.inj (otherEdge.symm.trans firstEdge)
  subst other
  have image := recorded_parallel_trace_image midReal agree (word := word.dropLast) (by
    intro factor hf
    obtain ⟨ss, atSs, width⟩ := widths factor hf
    exact ⟨ss, atSs, by omega⟩) trace
  have whole : evalWord (fun i => rankOrdinalAction (embedding i)) word.dropLast (theta x) =
      evalWord (fun i => rankOrdinalAction (embedding i)) front
        (theta (terminal + 1 + (sources.filter (· < x)).length)) := by
    have factors : word.dropLast = front ++ [terminal] := by rw [shape]; simp
    rw [factors, evalWord_append]
    change evalWord (fun i => rankOrdinalAction (embedding i)) front (rankOrdinalAction (embedding terminal) (theta x)) = _
    rw [scanRankReach_record_edges reach member (fun z hz => (bounds z hz).le) x hx]
  have exactEdge := (ownerEdges x hx).trans (whole.symm.trans image)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using exactEdge

end FullMarkedBLP


