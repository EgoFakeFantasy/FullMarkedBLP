import FullMarkedBLP.NativeTargetParallelEdge

namespace FullMarkedBLP

/-- A retained target block supplies the B-chain needed for parallel edges at
an actual scan step. Only earlier entrances and the current entrance are used. -/
theorem scan_step_record_parallel_predecessor {initial a b : Pattern}
    {rec : Records} {cursor : Nat} (reach : ScanReach initial a rec cursor)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ i row, rowAt (completeFrozenMarks a rec cursor) i = some row → row.CoreValid i)
    {terminal top k : Nat} {recorded sources : List Nat}
    (hm : (terminal, recorded) ∈ rec)
    (hn : native (completeFrozenMarks a rec cursor) cursor = some (b, sources))
    (hp : predecessor (completeFrozenMarks a rec cursor) cursor = some terminal)
    (entered : terminal + top ∈ sources) (htop : top ≤ recorded.length)
    (hk : 0 < k) (hkt : k ≤ top) :
    predecessor b (cursor + k) = some (terminal + k) := by
  apply native_target_segment_predecessor valid hn hp entered _ hk hkt
  intro j hj hjt
  have hb := scanReach_record_targets_before reach hm
  rw [completeFrozenMarks_other_row (by omega : terminal + j ≠ cursor)]
  exact scanReach_record_target_b reach entrances hm hj (by omega)

/-- The source-to-target parallel trace is literal, not an assumed packet field. -/
theorem scan_step_record_parallel_trace {initial a b : Pattern}
    {rec : Records} {cursor : Nat} (reach : ScanReach initial a rec cursor)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ i row, rowAt (completeFrozenMarks a rec cursor) i = some row → row.CoreValid i)
    {terminal top k : Nat} {recorded sources : List Nat}
    (hm : (terminal, recorded) ∈ rec)
    (hn : native (completeFrozenMarks a rec cursor) cursor = some (b, sources))
    (hp : predecessor (completeFrozenMarks a rec cursor) cursor = some terminal)
    (entered : terminal + top ∈ sources) (htop : top ≤ recorded.length)
    (hk : 0 < k) (hkt : k ≤ top) :
    Trace b (terminal + k) (cursor + k) [cursor + k, terminal + k] := by
  have edge := scan_step_record_parallel_predecessor reach entrances valid hm hn hp entered htop hk hkt
  exact Trace.next (predecessor_lt (native_preserves_coreValid valid hn) edge) edge Trace.stop

end FullMarkedBLP
