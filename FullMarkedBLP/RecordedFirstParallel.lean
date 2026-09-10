import FullMarkedBLP.RecordedParallelPredecessor
import FullMarkedBLP.RecordedLastEndpoint

namespace FullMarkedBLP

/-- Current +1 endpoint geometry supplies the first entered source automatically. -/
theorem scanReach_recorded_first_parallel_predecessor {initial a : Pattern} {rec : Records}
    {r upper lower : Nat} {upperSources lowerSources : List Nat}
    (reach : ScanReach initial a rec r)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (upperMem : (upper, upperSources) ∈ rec) (lowerMem : (lower, lowerSources) ∈ rec)
    (lt : lower < upper) (hp : predecessor a upper = some lower)
    {row : Row} (hr : rowAt a upper = some row) (he : row.e = some (lower + 1)) :
    predecessor a (upper + 1) = some (lower + 1) := by
  obtain ⟨bottom, last, atBottom, lastSource, endpoint⟩ :=
    scanReach_record_last_endpoint reach entrances upperMem
  have rows : bottom = row := Option.some.inj (atBottom.symm.trans hr)
  subst bottom
  have lastEq : last = lower + 1 := Option.some.inj (endpoint.symm.trans he)
  have entered : lower + 1 ∈ upperSources := by
    simpa only [lastEq] using List.mem_of_getLast? lastSource
  have nonempty : lowerSources ≠ [] :=
    ((scanReach_records_before reach).2 (lower, lowerSources) lowerMem).2.2
  have length : 0 < lowerSources.length := List.length_pos_iff.mpr nonempty
  exact scanReach_recorded_parallel_predecessor reach entrances upperMem lowerMem lt hp
    entered (by omega) (by decide) (by omega)

end FullMarkedBLP

