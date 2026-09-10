import FullMarkedBLP.CopyFrozenNewCertificate
import FullMarkedBLP.CompletionRowClosure

namespace FullMarkedBLP

/-- Every actual owner mark retains a natural-cutoff certificate after an
arbitrary-word frozen event, including all newly inserted marks. -/
theorem shortCopy_frozen_all_certificates {lambda : Ordinal.{u}} {parent copied a : Pattern}
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
    ∀ out, rowAt (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y) r = some out →
      ∀ z ∈ out.marks, ∃ xs delta,
        MarkTrace (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y) r z xs ∧
        naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
        rankCutoffAgreement delta.val (embedding r)
          (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  have event := shortCopy_frozen_event_geometry parentValid sat copy reach entryReal currentReal verified
    processed earlier events h hr hm currentAt
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
      have bound := List.mem_range.mp hj
      obtain ⟨xs, delta, trace, cutoff, agreement⟩ :=
        shortCopy_frozen_new_certificate parentValid sat copy reach entryReal currentReal verified
          processed earlier events h hr hm currentAt hc (by omega : 0 < j + 1) (by omega)
      rw [completeMark, currentAt, hc] at trace
      have target : y + (j + 1) = z := by omega
      exact ⟨xs, delta, by simpa only [target] using trace, cutoff, agreement⟩

end FullMarkedBLP
