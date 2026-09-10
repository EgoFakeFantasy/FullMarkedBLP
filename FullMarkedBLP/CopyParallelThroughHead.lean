import FullMarkedBLP.CopyRecordedInitialPacket

namespace FullMarkedBLP

/-- A property propagating forward from the head holds on the whole list. -/
theorem list_all_of_head_and_forward {P : Nat → Prop} {y : Nat} {tail : List Nat}
    (headHolds : P y)
    (forward : ∀ upper lower, (upper, lower) ∈ (y :: tail).zip tail → P upper → P lower) :
    ∀ x ∈ y :: tail, P x := by
  induction tail generalizing y with
  | nil => intro x mem; simpa using (List.mem_singleton.mp mem) ▸ headHolds
  | cons z rest ih =>
    have next := forward y z (by simp) headHolds
    have all := ih next (fun upper lower pair => forward upper lower
      (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr pair))
    intro x mem
    rcases List.mem_cons.mp mem with eq | mem
    · simpa only [eq] using headHolds
    · exact all x mem

/-- Every factor of a recorded word supports every offset supported by its
head record; each corresponding internal predecessor is a literal parallel edge. -/
theorem shortCopy_recorded_parallel_through_head {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r s y : Nat}
    {xs tail headSources : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanReach copied a rec r)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (trace : Trace a s y xs) (factors : xs.dropLast = y :: tail)
    (headRecord : (y, headSources) ∈ rec)
    (records : ∀ factor ∈ xs.dropLast, ∃ ss, (factor, ss) ∈ rec) :
    (∀ factor ∈ xs.dropLast, ∃ ss, (factor, ss) ∈ rec ∧ headSources.length ≤ ss.length) ∧
    ∀ k, 0 < k → k ≤ headSources.length →
      ∀ upper lower, (upper, lower) ∈ xs.dropLast.zip xs.dropLast.tail →
        predecessor a (upper + k) = some (lower + k) := by
  have originalEdges := trace_internal_predecessors trace
  have all : ∀ factor ∈ xs.dropLast, ∃ ss, (factor, ss) ∈ rec ∧ headSources.length ≤ ss.length := by
    rw [factors]
    apply list_all_of_head_and_forward (P := fun factor => ∃ ss, (factor, ss) ∈ rec ∧ headSources.length ≤ ss.length)
      ⟨headSources, headRecord, Nat.le_refl _⟩
    intro upper lower pair upperWidth
    have actualPair : (upper, lower) ∈ xs.dropLast.zip xs.dropLast.tail := by
      simpa only [factors, List.tail_cons] using pair
    obtain ⟨upperSources, upperMember, upperWidth⟩ := upperWidth
    obtain ⟨lowerSources, lowerMember⟩ := records lower
      (List.mem_of_mem_tail (List.of_mem_zip actualPair).2)
    have pred := originalEdges upper lower actualPair
    have width := (shortCopy_recorded_initial_packet parentValid sat copy reach entryReal verified
      upperMember lowerMember (predecessor_lt valid pred) pred).1
    exact ⟨lowerSources, lowerMember, by omega⟩
  refine ⟨all, ?_⟩
  intro k hk hkt upper lower pair
  obtain ⟨upperSources, upperMember, width⟩ := all upper (List.of_mem_zip pair).1
  obtain ⟨lowerSources, lowerMember⟩ := records lower
    (List.mem_of_mem_tail (List.of_mem_zip pair).2)
  have pred := originalEdges upper lower pair
  exact ((shortCopy_recorded_initial_packet parentValid sat copy reach entryReal verified
    upperMember lowerMember (predecessor_lt valid pred) pred).2 k hk (by omega)).2

end FullMarkedBLP
