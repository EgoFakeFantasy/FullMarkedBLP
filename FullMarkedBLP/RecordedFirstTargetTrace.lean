import FullMarkedBLP.ScanRecordedPredecessorPrior
import FullMarkedBLP.ScanRecordBirthPrefix

namespace FullMarkedBLP

/-- The least retained birth source closes the first parallel column literally. -/
theorem scanReach_record_first_target_trace {initial a : Pattern} {rec : Records}
    {r terminal x : Nat} {sources : List Nat} (reach : ScanReach initial a rec r)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (member : (terminal, sources) ∈ rec) (last : sources.getLast? = some x) :
    Trace a x (terminal + 1) [terminal + 1, x] := by
  obtain ⟨before, after, history, prior, _, birth, _⟩ := scanReach_record_origin_prefix reach member
  have bound := scanReach_record_targets_before reach member
  have decreasing := nativeSources_decreasing
    (entrances before history terminal prior (by omega)) (native_sources_of_success birth)
  have rank : (sources.filter (· < x)).length = 0 := by
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
  simpa only [rank, Nat.zero_add] using
    scanReach_record_trace_prior reach entrances member (List.mem_of_getLast? last)

end FullMarkedBLP
