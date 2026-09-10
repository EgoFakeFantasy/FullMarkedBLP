import FullMarkedBLP.CopyFrozenEventGeometry
import FullMarkedBLP.ScanFrozenWidthCutoff
import FullMarkedBLP.CompletionSemanticMarks

namespace FullMarkedBLP

/-- Each actual inserted mark of an arbitrary-word completion carries the
natural-cutoff certificate of its full parallel word. -/
theorem shortCopy_frozen_new_certificate {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y offset : Nat}
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
    (currentAt : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some currentRow)
    {sources : List Nat}
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources)
    (positive : 0 < offset) (width : offset ≤ sources.length) :
    ∃ word delta,
      MarkTrace (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y)
        r (y + offset) word ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta word.dropLast = some delta ∧
      rankCutoffAgreement delta.val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) word.dropLast) := by
  have event := shortCopy_frozen_event_geometry parentValid sat copy reach entryReal currentReal verified
    processed earlier events h hr hm currentAt
  obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
    event.2 currentRow sources currentAt hc
  obtain ⟨word, computed, widths, traces⟩ := shortCopy_frozen_completion_full_traces parentValid sat copy reach
    entryReal currentReal verified processed events hr hm hc
  obtain ⟨phi, mono, holds, records, certs⟩ := scanRankReach_frozen_bounded_historical_certificates reach
    entryReal (scanPriorVerifiedEvents_geometry verified) processed events h.valid hr
  obtain ⟨xs, delta, _, oldComputed, oldCutoff, _, saved⟩ := certs y hm
  have same : word = xs.map phi := Option.some.inj (computed.symm.trans oldComputed)
  subst word
  obtain ⟨x, member, rank, trace⟩ := traces offset positive width
  have rankEq : (sources.filter (· < x)).length + 1 = offset := by omega
  have marked := rankRealization_completion_new_markTrace h currentAt hp hk hy hnext hs bounds gap beforeOwner packet
    member (by simpa only [rankEq] using trace)
  have agree := scanEmbeddingReach_records_agree (scanRankReach_embeddings reach)
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have rb := rowAt_bounds hr
  have block : ∀ v ∈ xs.dropLast, ∃ ss, (phi v, ss) ∈ rec ∧ offset ≤ ss.length := by
    intro v hv
    have mapped : phi v ∈ (xs.map phi).dropLast := by
      rw [← List.map_dropLast]
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    obtain ⟨ss, record, sameWidth⟩ := widths (phi v) mapped
    exact ⟨ss, record, by omega⟩
  have factors : ∀ v ∈ xs.dropLast, embedding (phi v + offset) = initialEmbedding v := by
    intro v hv
    obtain ⟨ss, record, bound⟩ := block v hv
    exact (agree (phi v) ss record offset bound).trans (holds v).2
  have successors : ∀ v ∈ xs.dropLast, theta (phi v + offset + 1) ≤ initialTheta (v + 1) := by
    intro v hv
    obtain ⟨ss, record, bound⟩ := block v hv
    obtain ⟨i, image, successor⟩ := records (phi v) ss record
    have eq : i = v := mono.injective image
    subst i
    rw [← (holds (v + 1)).1, successor]
    have before := scanReach_record_targets_before plain record
    by_cases eq : offset = ss.length
    · simp only [eq, le_refl]
    · exact (currentReal.increasing _ _ (by omega) (by omega)).le
  have oldAgreement : rankCutoffAgreement delta.val (embedding r)
      (evalWord (fun i => (initialEmbedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
    intro z w hz hw
    have result := saved z w hz hw
    have reindex := evalWord_reindex
      (fun i => (initialEmbedding i : RankDomain lambda → RankDomain lambda))
      (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) phi xs.dropLast
      (fun i _ => by dsimp only; rw [(holds i).2]) w
    rw [reindex] at result
    exact result
  have nonempty : xs.dropLast ≠ [] := by
    intro empty
    rw [empty] at oldCutoff
    simp [naturalCutoff] at oldCutoff
  obtain ⟨newDelta, newCutoff⟩ := naturalCutoff_defined (fun i => rankOrdinalAction (embedding i)) theta
    (by
      intro empty
      have length := congrArg List.length empty
      simp only [List.length_map, List.length_nil] at length
      exact nonempty (List.length_eq_zero_iff.mp length)
      : xs.dropLast.map (fun i => phi i + offset) ≠ [])
  have certificate := rankCertificate_reindex initialEmbedding embedding initialTheta theta
    (fun i => phi i + offset) xs.dropLast (embedding r) factors successors oldCutoff newCutoff oldAgreement
  refine ⟨xs.dropLast.map (fun i => phi i + offset) ++ [x], newDelta, ?_, ?_, ?_⟩
  · rw [completeMark, currentAt, hc]
    simpa only [rankEq, ← List.map_dropLast, List.map_map, Function.comp_def] using marked
  · simpa only [List.dropLast_concat] using newCutoff
  · simpa only [List.dropLast_concat] using certificate

end FullMarkedBLP
