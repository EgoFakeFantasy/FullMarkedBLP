import FullMarkedBLP.CompletionFirstTrace
import FullMarkedBLP.CompletionSemanticMarks

namespace FullMarkedBLP

/-- The least source of a decreasing list has ascending rank zero. -/
theorem decreasing_last_rank_zero {sources : List Nat} {x : Nat}
    (decreasing : sources.Pairwise (· > ·)) (last : sources.getLast? = some x) :
    (sources.filter (· < x)).length = 0 := by
  obtain ⟨front, eq⟩ := List.getLast?_eq_some_iff.mp last
  have cross := (List.pairwise_append.mp (eq ▸ decreasing)).2.2
  have empty : sources.filter (· < x) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    obtain ⟨mem, lt⟩ := List.mem_filter.mp hz
    have lt' : z < x := by simpa using lt
    rw [eq] at mem
    rcases List.mem_append.mp mem with mem | mem
    · have := cross z mem x (by simp)
      omega
    · have : z = x := by simpa using mem
      omega
  simp only [empty, List.length_nil]

/-- Given verified event geometry, the first literal parallel word is an actual new mark. -/
theorem completionEvent_first_parallel_markTrace {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat} {sources : List Nat} (reach : ScanReach initial a rec r)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (event : CompletionEventGeometry a rec r y theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources)
    (records : ∀ xs, computeMarkTrace a r y = some xs →
      ∀ factor ∈ xs.dropLast, ∃ ss, (factor, ss) ∈ rec) :
    ∃ xs x, computeMarkTrace a r y = some xs ∧ sources.getLast? = some x ∧
      MarkTrace (completeMark a rec r y) r (y + 1)
        (xs.dropLast.map (fun i => i + 1) ++ [x]) := by
  obtain ⟨xs, x, computed, last, trace⟩ :=
    completionRecord_first_parallel_trace reach event.1.valid entrances hr hm hc records
  obtain ⟨word, terminal, _, _, recorded, _, _⟩ := completionRecord_iff.mp hc
  have member := recordAt_mem recorded
  obtain ⟨before, after, history, prior, _, birth, _⟩ := scanReach_record_origin_prefix reach member
  have bound := scanReach_record_targets_before reach member
  have decreasing := nativeSources_decreasing
    (entrances before history terminal prior (by omega)) (native_sources_of_success birth)
  have rank := decreasing_last_rank_zero decreasing last
  obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
    event.2 row sources hr hc
  have marked := rankRealization_completion_new_markTrace event.1 hr hp hk hy hnext hs
    bounds gap beforeOwner packet (List.mem_of_getLast? last)
    (by simpa only [rank, Nat.zero_add] using trace)
  refine ⟨xs, x, computed, last, ?_⟩
  rw [completeMark, hr, hc]
  simpa only [rank, Nat.zero_add] using marked

end FullMarkedBLP
