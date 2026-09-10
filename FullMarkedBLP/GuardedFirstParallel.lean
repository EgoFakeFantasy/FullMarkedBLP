import FullMarkedBLP.RecordedFirstParallel

namespace FullMarkedBLP

/-- All internal edges of a guarded recorded word have their first parallel edge. -/
theorem currentPlusOne_recorded_first_parallel_edges {initial a : Pattern} {rec : Records}
    {r s y : Nat} {xs : List Nat} (reach : ScanReach initial a rec r)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (trace : Trace a s y xs) (guard : currentPlusOne a xs = true)
    (records : ∀ factor ∈ xs.dropLast, ∃ sources, (factor, sources) ∈ rec) :
    ∀ upper lower, (upper, lower) ∈ xs.dropLast.zip xs.dropLast.tail →
      predecessor a (upper + 1) = some (lower + 1) := by
  intro upper lower pair
  obtain ⟨row, hr, hp, he⟩ := currentPlusOne_all_endpoints valid trace guard upper lower pair
  have members := List.of_mem_zip pair
  obtain ⟨upperSources, upperMem⟩ := records upper members.1
  obtain ⟨lowerSources, lowerMem⟩ := records lower (List.mem_of_mem_tail members.2)
  have hv := valid upper row hr
  have lt : lower < upper := fromRight_lt_last hv.1 hv.2.2.1
    (by have := hv.2.2.2.1; omega : 1 < row.step + 1) hp
  have pred : predecessor a upper = some lower := by
    simp only [predecessor, hr, Option.bind_some]
    exact hp
  exact scanReach_recorded_first_parallel_predecessor reach entrances upperMem lowerMem lt pred hr he

end FullMarkedBLP
