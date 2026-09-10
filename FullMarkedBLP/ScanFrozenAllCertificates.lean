import FullMarkedBLP.ScanFrozenDirectCertificate

namespace FullMarkedBLP

/-- All actual owner marks after a direct intermediate event have natural-cutoff certificates. -/
theorem scanRankReach_frozen_direct_all_certificates {lambda : Ordinal.{u}} {initial a : Pattern}
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
    ∀ out, rowAt (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y) r = some out →
      ∀ z ∈ out.marks, ∃ xs delta,
        MarkTrace (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y) r z xs ∧
        naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
        rankCutoffAgreement delta.val (embedding r)
          (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  have event := scanRankReach_frozen_direct_event_geometry reach entryRealization geometry
    processed earlier events h hr hm currentAt ht
  cases hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y with
  | none =>
    intro out hout z hz
    rw [completeMark, currentAt, hc] at hout ⊢
    have eq := Option.some.inj (hout.symm.trans currentAt)
    subst out
    obtain ⟨k, source, xs, delta, hk, hky, hks, trace, cutoff, agreement⟩ := h.marked r currentRow z currentAt hz
    exact ⟨xs, delta, ⟨currentRow, k, source, currentAt, hz, hk, hky, hks, trace⟩, cutoff, agreement⟩
  | some sources =>
    obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
      event.2 currentRow sources currentAt hc
    intro out hout z hz
    rw [completeMark, currentAt, hc] at hout ⊢
    rw [rowAt_set_self currentAt] at hout
    cases Option.some.inj hout
    simp only [completeMarkRow, mem_canonicalColumns, List.mem_append] at hz
    rcases hz with old | inserted
    · exact rankRealization_completion_old_certificates h currentAt hp hk hy hnext hs bounds gap beforeOwner packet
        z (List.mem_filter.mp old).1
    · obtain ⟨j, hj, he⟩ := List.mem_map.mp inserted
      obtain ⟨x, hx, rank⟩ := exists_source_at_rank hs (List.mem_range.mp hj)
      obtain ⟨xs, delta, trace, cutoff, agreement⟩ :=
        scanRankReach_frozen_direct_new_certificate reach entryRealization geometry
          processed earlier events h hr hm currentAt ht hc hx
      rw [completeMark, currentAt, hc] at trace
      have target : y + ((sources.filter (· < x)).length + 1) = z := by omega
      exact ⟨xs, delta, by simpa only [target] using trace, cutoff, agreement⟩

end FullMarkedBLP
