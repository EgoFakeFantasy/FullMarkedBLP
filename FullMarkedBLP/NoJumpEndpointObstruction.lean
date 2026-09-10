import FullMarkedBLP.CompletionAtEndpoint
import FullMarkedBLP.ScanRecords
import FullMarkedBLP.ScanRecordOrigin

namespace FullMarkedBLP

/-- A shorter completion at B would violate a global no-interior-jump invariant
for B's own larger retained block. This is conditional, not a reachable example. -/
theorem shorter_endpoint_completion_enters_record_interior {lambda : Ordinal.{u}}
    {initial a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r base : Nat}
    {block sources : List Nat} (reach : ScanReach initial a rec r)
    (event : CompletionEventGeometry a rec r base theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hb : row.b = some base)
    (record : (base, block) ∈ rec) (hc : completionRecord a rec r base = some sources)
    (positive : 0 < sources.length) (shorter : sources.length < block.length) :
    base + block.length < r ∧
      (rowAt (completeMark a rec r base) r).bind Row.b = some (base + sources.length) ∧
      base < base + sources.length ∧ base + sources.length < base + block.length := by
  have ownerBound := scanReach_record_targets_before reach record
  have result := completionEvent_b_at_b event hr hb hc
  refine ⟨ownerBound, ?_, by omega, by omega⟩
  rw [completeMark, hr, hc, rowAt_set_self hr]
  exact result

end FullMarkedBLP
