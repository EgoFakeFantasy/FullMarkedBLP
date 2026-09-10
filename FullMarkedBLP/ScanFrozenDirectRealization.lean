import FullMarkedBLP.ScanFrozenAllCertificates
import FullMarkedBLP.CompletionEventEdges
import FullMarkedBLP.FrozenPredecessorGeometry

namespace FullMarkedBLP

/-- Full row realization survives an actual direct intermediate frozen event. -/
theorem scanRankReach_frozen_direct_realization {lambda : Ordinal.{u}} {initial a : Pattern}
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
    (ht : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some [y, s]) : RankRowRealization
      (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y) theta embedding := by
  have event := scanRankReach_frozen_direct_event_geometry reach entryRealization geometry
    processed earlier events h hr hm currentAt ht
  have certificates := scanRankReach_frozen_direct_all_certificates reach entryRealization geometry
    processed earlier events h hr hm currentAt ht
  obtain ⟨phi, _, _, _, certs⟩ := scanRankReach_current_historical_certificates reach entryRealization geometry hr
  obtain ⟨xs, delta, oldTrace, _, _, _⟩ := certs y hm
  obtain ⟨current, _, _, hcAt, currentMark, _⟩ := frozen_fold_preserves_historical_trace processed events oldTrace
  have eq := Option.some.inj (hcAt.symm.trans currentAt)
  subst current
  have entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i := by
    intro before history owner prior bound
    obtain ⟨oldTheta, oldEmbedding, lifted⟩ := scanReach_rank_lift prior initialTheta initialEmbedding
    exact (geometry before history owner oldTheta oldEmbedding lifted bound).1
  have edges := completionEvent_frozen_prefix_all_edges entrances
    (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) processed event currentAt currentMark
  have valid := completionEvent_coreValid event
  have pred := completionEvent_preserves_predecessors event
  generalize hb : processed.foldl (fun current z => completeMark current rec r z) a = b at h currentAt ht event certificates edges valid pred ⊢
  cases hc : completionRecord b rec r y with
  | none => simpa only [completeMark, currentAt, hc] using h
  | some sources =>
    obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
      event.2 currentRow sources currentAt hc
    have hlen : 0 < currentRow.core.length := by have := (h.valid r currentRow currentAt).2.1; omega
    let minimum := currentRow.core[0]'hlen
    have hmin : currentRow.core.head? = some minimum := by simp [List.head?_eq_getElem?, minimum]
    obtain ⟨proper, minimumEq, critical⟩ := rankRealization_completion_marks_critical h currentAt hp currentMark hmin
      hk hy hnext hs bounds gap beforeOwner packet
    simp only [completeMark, currentAt, hc] at valid edges certificates pred ⊢
    refine ⟨valid, ?_, ?_, ?_, edges, ?_, ?_⟩
    · intro i out hout
      by_cases hi : i = r
      · subst i
        rw [rowAt_set_self currentAt] at hout
        cases Option.some.inj hout
        exact proper
      · rw [rowAt_set_other currentAt hi] at hout
        exact h.proper i out hout
    · intro i j hij hj
      exact h.increasing i j hij (by simpa only [List.length_set] using hj)
    · intro i hi
      exact h.cardinals i (by simpa only [List.length_set] using hi)
    · intro i out low hout hlow
      by_cases hi : i = r
      · subst i
        rw [rowAt_set_self currentAt] at hout
        cases Option.some.inj hout
        have eq := Option.some.inj (minimumEq.symm.trans hlow)
        subst low
        exact critical
      · rw [rowAt_set_other currentAt hi] at hout
        exact h.critical i out low hout hlow
    · intro i out z hout hz
      by_cases hi : i = r
      · subst i
        obtain ⟨xs, delta, mark, cutoff, agreement⟩ := certificates out hout z hz
        obtain ⟨actual, j, source, hactual, _, hj, hzy, hsource, trace⟩ := mark
        have eq := Option.some.inj (hactual.symm.trans hout)
        subst actual
        exact ⟨j, source, xs, delta, hj, hzy, hsource, trace, cutoff, agreement⟩
      · have old := hout
        rw [rowAt_set_other currentAt hi] at old
        obtain ⟨j, source, xs, delta, hj, hzy, hsource, trace, cutoff, agreement⟩ := h.marked i out z old hz
        refine ⟨j, source, xs, delta, hj, hzy, hsource, ?_, cutoff, agreement⟩
        have moved := trace_map (b := b.set (r - 1) (completeMarkRow currentRow y sources))
          id (fun hlt => hlt) trace (by
            intro x w _ hw
            simpa only [id_eq, pred x] using hw)
        simpa only [List.map_id, id_eq] using moved

end FullMarkedBLP

