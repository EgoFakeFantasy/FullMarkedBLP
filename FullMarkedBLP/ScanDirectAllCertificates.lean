import FullMarkedBLP.ScanDirectEventGeometry
import FullMarkedBLP.ScanDirectNewCertificate
import FullMarkedBLP.CompletionRowClosure

namespace FullMarkedBLP

/-- Every mark in the actual completed owner row has a natural-cutoff
certificate, combining retained historical marks and inserted packet marks. -/
theorem scanRankReach_direct_all_certificates {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (h : RankRowRealization a theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (ht : computeMarkTrace a r y = some [y, s]) :
    ∀ out, rowAt (completeMark a rec r y) r = some out → ∀ z ∈ out.marks,
      ∃ xs delta, MarkTrace (completeMark a rec r y) r z xs ∧
        naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
        rankCutoffAgreement delta.val (embedding r)
          (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  have event := scanRankReach_direct_event_geometry reach entryRealization geometry h hr hm ht
  cases hc : completionRecord a rec r y with
  | none =>
    intro out hout z hz
    simp only [completeMark, hr, hc] at hout ⊢
    have heq := Option.some.inj hout
    subst out
    obtain ⟨k, source, xs, delta, hk, hky, hks, trace, cutoff, agreement⟩ := h.marked r row z hr hz
    exact ⟨xs, delta, ⟨row, k, source, hr, hz, hk, hky, hks, trace⟩, cutoff, agreement⟩
  | some sources =>
    obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
      event.2 row sources hr hc
    intro out hout z hz
    simp only [completeMark, hr, hc] at hout ⊢
    rw [rowAt_set_self hr] at hout
    cases Option.some.inj hout
    simp only [completeMarkRow, mem_canonicalColumns, List.mem_append] at hz
    rcases hz with old | inserted
    · exact rankRealization_completion_old_certificates h hr hp hk hy hnext hs bounds gap beforeOwner packet
        z (List.mem_filter.mp old).1
    · obtain ⟨j, hj, he⟩ := List.mem_map.mp inserted
      obtain ⟨x, hx, rank⟩ := exists_source_at_rank hs (List.mem_range.mp hj)
      obtain ⟨xs, delta, trace, cutoff, _, agreement⟩ :=
        scanRankReach_direct_new_certificate reach entryRealization geometry h hr hm ht hc hx
      have target : y + ((sources.filter (· < x)).length + 1) = z := by omega
      exact ⟨xs, delta, by simpa only [target] using trace, cutoff, agreement⟩

end FullMarkedBLP

