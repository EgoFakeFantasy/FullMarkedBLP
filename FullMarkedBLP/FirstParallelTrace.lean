import FullMarkedBLP.GuardedFirstParallel
import FullMarkedBLP.RecordedFirstTargetTrace

namespace FullMarkedBLP

/-- Assemble an actual trace from a nonempty factor chain and its terminal edge. -/
theorem trace_of_factor_chain {a : Pattern} {x y : Nat} {tail : List Nat}
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (edges : ∀ upper lower, (upper, lower) ∈ (y :: tail).zip tail →
      predecessor a upper = some lower)
    (lastEdge : ∀ z, (y :: tail).getLast? = some z → predecessor a z = some x) :
    Trace a x y ((y :: tail) ++ [x]) := by
  induction tail generalizing y with
  | nil =>
    have edge := lastEdge y rfl
    exact Trace.next (predecessor_lt valid edge) edge Trace.stop
  | cons z rest ih =>
    have edge := edges y z (by simp)
    have ht := ih
      (fun upper lower pair => edges upper lower (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr pair))
      (fun w hw => lastEdge w (by simpa using hw))
    have low := trace_source_le_head ht
    have high := predecessor_lt valid edge
    exact Trace.next (by omega) edge ht

/-- The first column is a complete literal trace, under retained-factor records. -/
theorem currentPlusOne_recorded_first_trace {initial a : Pattern} {rec : Records}
    {r s y terminal x : Nat} {xs tail sources : List Nat} (reach : ScanReach initial a rec r)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (trace : Trace a s y xs) (guard : currentPlusOne a xs = true)
    (factors : xs.dropLast = y :: tail)
    (lastFactor : (y :: tail).getLast? = some terminal)
    (records : ∀ factor ∈ xs.dropLast, ∃ ss, (factor, ss) ∈ rec)
    (member : (terminal, sources) ∈ rec) (lastSource : sources.getLast? = some x) :
    Trace a x (y + 1) ((xs.dropLast.map (fun i => i + 1)) ++ [x]) := by
  have internal := currentPlusOne_recorded_first_parallel_edges reach valid entrances trace guard records
  have terminalTrace := scanReach_record_first_target_trace reach entrances member lastSource
  have terminalEdge : predecessor a (terminal + 1) = some x := by
    cases terminalTrace with
    | next _ hp ht =>
      have eq := Option.some.inj (trace_head ht)
      simpa only [← eq] using hp
  rw [factors, List.map_cons]
  apply trace_of_factor_chain valid
  · intro upper lower pair
    have mapped : (upper, lower) ∈ ((y :: tail).map (fun i => i + 1)).zip
        (tail.map (fun i => i + 1)) := pair
    rw [List.zip_map] at mapped
    obtain ⟨⟨u, v⟩, uv, eq⟩ := List.mem_map.mp mapped
    cases eq
    apply internal u v
    simpa only [factors, List.tail_cons] using uv
  · intro z hz
    have hzMap : ((y :: tail).map (fun i => i + 1)).getLast? = some z := hz
    have hz' : some (terminal + 1) = some z := by
      simpa only [List.getLast?_map, lastFactor, Option.map_some] using hzMap
    have eq := Option.some.inj hz'
    simpa only [← eq] using terminalEdge

end FullMarkedBLP

