import FullMarkedBLP.CopyPacketOwnerEdges

namespace FullMarkedBLP

/-- A successful arbitrary-word frozen completion has its full event geometry.
The hypotheses verify strictly earlier scan events and earlier frozen marks;
the current event is a conclusion. -/
theorem shortCopy_frozen_event_geometry {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    (processed : List Nat) (earlier : ∀ z ∈ processed, z < y)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (h : RankRowRealization (processed.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    {row currentRow : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (currentAt : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some currentRow) :
    CompletionEventGeometry (processed.foldl (fun current z => completeMark current rec r z) a)
      rec r y theta embedding := by
  obtain ⟨j, source, xs, delta, hj, hy, hsource, trace, cutoff, agreement⟩ := currentReal.marked r row y hr hm
  have originalY : y ∈ row.core := List.mem_of_getElem? hy
  have oldTrace : MarkTrace a r y xs := ⟨row, j, source, hr, hm, hj, hy, hsource, trace⟩
  obtain ⟨current, _, _, hcAt, currentMark, _⟩ := frozen_fold_preserves_historical_trace processed events oldTrace
  have currentEq := Option.some.inj (hcAt.symm.trans currentAt)
  subst current
  refine ⟨h, ?_⟩
  intro other sources hother hc
  have eq := Option.some.inj (hother.symm.trans currentAt)
  subst other
  have valid := h.valid r currentRow currentAt
  obtain ⟨k, hk, hky⟩ := (h.proper r currentRow currentAt).2 y currentMark |>.2
  have stepBound := Row.step_lt_length valid.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := currentRow.core) (k := currentRow.step + 1) (by omega) (by omega)
  have index := (List.getElem?_eq_some_iff.mp hky).1
  have nextIndex : k + 1 < (currentRow.full r).length := by simp [Row.full]; omega
  let nextTarget := (currentRow.full r)[k + 1]
  have hnt : (currentRow.full r)[k + 1]? = some nextTarget := List.getElem?_eq_getElem nextIndex
  obtain ⟨word, computed, widths, _⟩ := shortCopy_frozen_completion_full_traces parentValid sat copy reach
    entryReal currentReal verified processed events hr hm hc
  obtain ⟨otherWord, terminal, otherComputed, atTerminal, terminalRecord, _, _⟩ := completionRecord_iff.mp hc
  have same : otherWord = word := Option.some.inj (otherComputed.symm.trans computed)
  subst otherWord
  obtain ⟨front, last, shape⟩ := fromRight_two_decomposition atTerminal
  obtain ⟨_, _, _, _, _, _, _, _, currentTrace⟩ := computeMarkTrace_sound currentAt currentMark computed
  have head := trace_head currentTrace
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
  obtain ⟨headSources, headRecord, width⟩ := widths y member
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have record := recordAt_mem terminalRecord
  have beforeOwner := scanReach_record_targets_before plain headRecord
  have geometry := scanPriorVerifiedEvents_geometry verified
  have sourceBounds := scanRankReach_record_source_bounds reach
    (fun before history owner oldTheta oldEmbedding prior bound =>
      (geometry before history owner oldTheta oldEmbedding prior bound).1) record
  have rb := rowAt_bounds currentAt
  have terminalBound := (scanReach_records_before plain).2 (terminal, sources) record |>.2.1
  have fullY : (currentRow.full r)[k]? = some y := by
    unfold Row.full
    rw [List.getElem?_append_left index]
    exact hky
  obtain ⟨fi, fy⟩ := List.getElem?_eq_some_iff.mp fullY
  obtain ⟨ni, nt⟩ := List.getElem?_eq_some_iff.mp hnt
  have later := List.pairwise_iff_getElem.mp (coreValid_full_sorted valid) k (k + 1) fi ni (by omega)
  rw [fy, nt] at later
  have gap := scanRankReach_frozen_record_gap reach processed earlier events hr originalY currentAt headRecord
    (List.mem_of_getElem? hnt) later
  refine ⟨k, p, nextTarget, hp, hk, hky, hnt, scanReach_record_nodup plain record,
    ?_, by omega, by omega,
    shortCopy_frozen_completion_packet_edges parentValid sat copy reach entryReal currentReal verified
      processed events h hr hm hc⟩
  intro x hx
  have bound := sourceBounds x hx
  omega

end FullMarkedBLP
