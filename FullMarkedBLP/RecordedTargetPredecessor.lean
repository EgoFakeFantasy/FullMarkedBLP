import FullMarkedBLP.NativeWalkUnique
import FullMarkedBLP.ScanRecordedPredecessorPrior
import FullMarkedBLP.CompletionRowClosure

namespace FullMarkedBLP

/-- Every interior recorded target points to a birth source below the block base. -/
theorem scanReach_record_target_predecessor_below_base {initial a : Pattern} {rec : Records}
    {r owner k : Nat} {sources : List Nat} (reach : ScanReach initial a rec r)
    (entrances : ∀ before history cursor, ScanReach initial before history cursor → cursor < r →
      ∀ i row, rowAt (completeFrozenMarks before history cursor) i = some row → row.CoreValid i)
    (member : (owner, sources) ∈ rec) (positive : 0 < k) (bound : k ≤ sources.length) :
    ∃ x ∈ sources, x < owner ∧ predecessor a (owner + k) = some x := by
  obtain ⟨x, mem, rank⟩ := exists_source_at_rank (scanReach_record_nodup reach member)
    (j := k - 1) (by omega)
  have edge := scanReach_record_predecessor_prior reach entrances member mem
  have lower := scanReach_record_sources_below_prior reach entrances member x mem
  refine ⟨x, mem, lower, ?_⟩
  simpa only [rank, show k - 1 + 1 = k by omega] using edge

end FullMarkedBLP

