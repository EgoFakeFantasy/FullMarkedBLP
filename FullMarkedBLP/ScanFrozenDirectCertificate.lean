import FullMarkedBLP.ScanFrozenDirectGeometry

namespace FullMarkedBLP

/-- Actual inserted marks at a direct frozen-prefix event receive natural-cutoff certificates. -/
theorem scanRankReach_frozen_direct_new_certificate {lambda : Ordinal.{u}} {initial a : Pattern}
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
    (ht : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some [y, s])
    {sources : List Nat} {x : Nat}
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources)
    (hx : x ∈ sources) :
    ∃ xs delta,
      MarkTrace (completeMark (processed.foldl (fun current z => completeMark current rec r z) a) rec r y)
        r (y + ((sources.filter (· < x)).length + 1)) xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  have event := scanRankReach_frozen_direct_event_geometry reach entryRealization geometry
    processed earlier events h hr hm currentAt ht
  obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
    event.2 currentRow sources currentAt hc
  have entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i := by
    intro before history owner prior bound
    obtain ⟨oldTheta, oldEmbedding, lifted⟩ := scanReach_rank_lift prior initialTheta initialEmbedding
    exact (geometry before history owner oldTheta oldEmbedding lifted bound).1
  have record := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  have trace := scanReach_record_trace_frozen_prefix
    (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) entrances processed record hx
  have mark := rankRealization_completion_new_markTrace h currentAt hp hk hy hnext hs bounds gap beforeOwner packet hx trace
  have saved := scanRankReach_frozen_direct_endpoint_agreement reach entryRealization geometry
    processed events hr hm currentAt (h.valid r currentRow currentAt).1 ht hc
  have rank : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have rb := rowAt_bounds currentAt
  have covered : theta (y + ((sources.filter (· < x)).length + 1) + 1) ≤ theta (y + sources.length + 1) := by
    by_cases eq : (sources.filter (· < x)).length + 1 = sources.length
    · have index : y + ((sources.filter (· < x)).length + 1) + 1 = y + sources.length + 1 := by omega
      rw [index]
    · exact (h.increasing _ _ (by omega) (by omega)).le
  have cert := scan_record_direct_natural_certificate (scanRankReach_embeddings reach) record
    (by omega : (sources.filter (· < x)).length + 1 ≤ sources.length) (embedding r) saved covered
  refine ⟨[y + ((sources.filter (· < x)).length + 1), x],
    theta (y + ((sources.filter (· < x)).length + 1) + 1), ?_, cert.1, cert.2⟩
  rw [completeMark, currentAt, hc]
  exact mark

end FullMarkedBLP

