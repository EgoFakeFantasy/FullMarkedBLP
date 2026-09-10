import FullMarkedBLP.ScanFrozenDirectPacket
import FullMarkedBLP.CompletionHighColumns

namespace FullMarkedBLP

/-- A direct event at an earlier-completed frozen prefix obtains all packet
and gap witnesses from history, without assuming its event geometry. -/
theorem scanRankReach_frozen_direct_event_geometry {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (processed : List Nat) (earlier : ∀ z ∈ processed, z < y)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (h : RankRowRealization (processed.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    {row currentRow : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (currentAt : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some currentRow)
    (ht : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some [y, s]) :
    CompletionEventGeometry (processed.foldl (fun current z => completeMark current rec r z) a)
      rec r y theta embedding := by
  obtain ⟨phi, _, _, _, certs⟩ := scanRankReach_current_historical_certificates reach entryRealization geometry hr
  obtain ⟨xs, delta, oldTrace, _, _, _⟩ := certs y hm
  have oldTraceCopy := oldTrace
  obtain ⟨old, j, source, oldAt, _, _, oldY, _, _⟩ := oldTraceCopy
  have oldEq := Option.some.inj (oldAt.symm.trans hr)
  subst old
  have originalY : y ∈ row.core := List.mem_of_getElem? oldY
  have transported := frozen_fold_preserves_historical_trace processed events oldTrace
  obtain ⟨current, _, _, hcAt, currentMark, _⟩ := transported
  have currentEq := Option.some.inj (hcAt.symm.trans currentAt)
  subst current
  refine ⟨h, ?_⟩
  intro other sources hother hc
  have eq := Option.some.inj (hother.symm.trans currentAt)
  subst other
  have valid := h.valid r currentRow currentAt
  obtain ⟨k, hk, hy⟩ := (h.proper r currentRow currentAt).2 y currentMark |>.2
  have stepBound := Row.step_lt_length valid.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := currentRow.core) (k := currentRow.step + 1) (by omega) (by omega)
  have index := (List.getElem?_eq_some_iff.mp hy).1
  have nextIndex : k + 1 < (currentRow.full r).length := by simp [Row.full]; omega
  let nextTarget := (currentRow.full r)[k + 1]
  have hnt : (currentRow.full r)[k + 1]? = some nextTarget := List.getElem?_eq_getElem nextIndex
  have record := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  have unlabelled := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have beforeOwner := scanReach_record_targets_before unlabelled record
  have sourceBounds := scanRankReach_record_source_bounds reach
    (fun before history owner oldTheta oldEmbedding prior bound =>
      (geometry before history owner oldTheta oldEmbedding prior bound).1) record
  have rb := rowAt_bounds currentAt
  have fullY : (currentRow.full r)[k]? = some y := by
    unfold Row.full
    rw [List.getElem?_append_left index]
    exact hy
  obtain ⟨fi, fy⟩ := List.getElem?_eq_some_iff.mp fullY
  obtain ⟨ni, nt⟩ := List.getElem?_eq_some_iff.mp hnt
  have later := List.pairwise_iff_getElem.mp (coreValid_full_sorted valid) k (k + 1) fi ni (by omega)
  rw [fy, nt] at later
  have increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j := by
    intro i j hij hj
    exact h.increasing i j hij (by simpa only [completeMarks_fold_length] using hj)
  refine ⟨k, p, nextTarget, hp, hk, hy, hnt, scanReach_record_nodup unlabelled record,
    ?_, scanRankReach_frozen_record_gap reach processed earlier events hr originalY currentAt record
      (List.mem_of_getElem? hnt) later, beforeOwner,
    scanRankReach_frozen_direct_owner_packet reach entryRealization geometry increasing processed events
      hr hm currentAt valid.1 ht hc⟩
  intro x hx
  have bound := sourceBounds x hx
  omega

end FullMarkedBLP
