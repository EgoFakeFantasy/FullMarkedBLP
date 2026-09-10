import FullMarkedBLP.CompletionSemanticMarks
import FullMarkedBLP.ScanRecordedPredecessorPrior

namespace FullMarkedBLP

/-- In the direct branch, the actual completion record discharges the parallel
trace, distinctness, source bounds, and target-before-owner obligations. -/
theorem scan_completion_direct_new_markTrace {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r : Nat} (reach : ScanReach initial a rec r)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (h : RankRowRealization a theta embedding)
    {k y p nextTarget s x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (ht : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources)
    (gap : y + sources.length < nextTarget)
    (packet : ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length))
    (hx : x ∈ sources) :
    MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r
      (y + ((sources.filter (· < x)).length + 1))
      [y + ((sources.filter (· < x)).length + 1), x] := by
  have hm := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  have beforeOwner := scanReach_record_targets_before reach hm
  have sourceBounds := scanReach_record_sources_below_prior reach entrances hm
  have rb := rowAt_bounds hr
  exact rankRealization_completion_new_markTrace h hr hp hk hy hnt
    (scanReach_record_nodup reach hm)
    (fun z hz => by have hb := sourceBounds z hz; omega)
    gap beforeOwner packet hx (scanReach_record_trace_prior reach entrances hm hx)

end FullMarkedBLP
