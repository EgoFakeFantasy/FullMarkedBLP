import FullMarkedBLP.CopyParallelThroughHead
import FullMarkedBLP.FirstParallelTrace
import FullMarkedBLP.CompletionRowClosure
import FullMarkedBLP.NativeWalkUnique
import FullMarkedBLP.RecordUnique

namespace FullMarkedBLP

/-- Every offset within the head packet yields its whole literal parallel trace,
ending at the terminal source of the same ascending rank. -/
theorem shortCopy_recorded_trace_through_head {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r s y terminal k : Nat}
    {xs tail headSources sources : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanReach copied a rec r)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (trace : Trace a s y xs) (factors : xs.dropLast = y :: tail)
    (headRecord : (y, headSources) ∈ rec)
    (records : ∀ factor ∈ xs.dropLast, ∃ ss, (factor, ss) ∈ rec)
    (lastFactor : (y :: tail).getLast? = some terminal) (terminalRecord : (terminal, sources) ∈ rec)
    (positive : 0 < k) (width : k ≤ headSources.length) :
    ∃ x ∈ sources, (sources.filter (· < x)).length = k - 1 ∧
      Trace a x (y + k) ((xs.dropLast.map (fun i => i + k)) ++ [x]) := by
  obtain ⟨sizes, internal⟩ := shortCopy_recorded_parallel_through_head parentValid sat copy reach entryReal verified
    valid trace factors headRecord records
  have terminalMember : terminal ∈ xs.dropLast := by
    rw [factors]
    exact List.mem_of_getLast? lastFactor
  obtain ⟨ss, ssRecord, ssWidth⟩ := sizes terminal terminalMember
  have same := scanReach_record_unique reach ssRecord terminalRecord
  subst ss
  obtain ⟨x, member, rank⟩ := exists_source_at_rank (scanReach_record_nodup reach terminalRecord)
    (j := k - 1) (by omega)
  have geometry := scanPriorVerifiedEvents_geometry verified
  have historyValid : ∀ before history owner, ScanReach copied before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i := by
    intro before history owner reached earlier
    obtain ⟨theta, embedding, labelled⟩ := scanReach_rank_lift reached initialTheta initialEmbedding
    exact (geometry before history owner theta embedding labelled earlier).1
  have terminalEdge := scanReach_record_predecessor_prior reach historyValid terminalRecord member
  rw [rank, Nat.sub_add_cancel positive] at terminalEdge
  refine ⟨x, member, rank, ?_⟩
  rw [factors, List.map_cons]
  apply trace_of_factor_chain valid
  · intro upper lower pair
    have mapped : (upper, lower) ∈ ((y :: tail).map (fun i => i + k)).zip
        (tail.map (fun i => i + k)) := pair
    rw [List.zip_map] at mapped
    obtain ⟨⟨u, v⟩, uv, eq⟩ := List.mem_map.mp mapped
    cases eq
    apply internal k positive width u v
    simpa only [factors, List.tail_cons] using uv
  · intro z hz
    have hzMap : ((y :: tail).map (fun i => i + k)).getLast? = some z := hz
    have hz' : some (terminal + k) = some z := by
      simpa only [List.getLast?_map, lastFactor, Option.map_some] using hzMap
    have eq := Option.some.inj hz'
    simpa only [← eq] using terminalEdge

end FullMarkedBLP
