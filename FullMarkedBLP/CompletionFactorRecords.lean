import FullMarkedBLP.CompletionFirstTrace
import FullMarkedBLP.MarkEndpointRecordPropagation

namespace FullMarkedBLP

/-- A property propagating backwards across adjacent entries holds on the whole list. -/
theorem list_all_of_last_and_backward {P : Nat → Prop} {xs : List Nat} {last : Nat}
    (lastAt : xs.getLast? = some last) (lastHolds : P last)
    (backward : ∀ upper lower, (upper, lower) ∈ xs.zip xs.tail → P lower → P upper) :
    ∀ x ∈ xs, P x := by
  induction xs with
  | nil => simp at lastAt
  | cons y rest ih =>
    cases rest with
    | nil =>
      have eq : y = last := by simpa using lastAt
      intro x mem
      have xy : x = y := by simpa using mem
      simpa only [xy, eq] using lastHolds
    | cons z tail =>
      have tailLast : (z :: tail).getLast? = some last := by simpa using lastAt
      have tailAll := ih tailLast (fun upper lower pair => backward upper lower
        (by simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr pair))
      have headHolds := backward y z (by simp) (tailAll z (by simp))
      intro x mem
      rcases List.mem_cons.mp mem with eq | mem
      · simpa only [eq] using headHolds
      · exact tailAll x mem

/-- Every factor in an actual successful original marked word has a retained record. -/
theorem scanRankReach_completion_all_factor_records {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    {sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization initial initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (transport : ScanPriorEndpointTransport initial initialTheta initialEmbedding r)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources) :
    ∀ word, computeMarkTrace a r y = some word →
      ∀ factor ∈ word.dropLast, ∃ ss, (factor, ss) ∈ rec := by
  obtain ⟨word, marked, computed, propagation⟩ :=
    scanRankReach_mark_endpoint_record_propagation reach entryReal currentReal geometry transport hr hm
  obtain ⟨other, terminal, otherComputed, atTerminal, record, _, guard⟩ := completionRecord_iff.mp hc
  have eq : other = word := Option.some.inj (otherComputed.symm.trans computed)
  subst other
  obtain ⟨front, last, shape⟩ := fromRight_two_decomposition atTerminal
  have lastFactor : word.dropLast.getLast? = some terminal := by rw [shape]; simp
  have lastRecord : ∃ ss, (terminal, ss) ∈ rec := ⟨sources, recordAt_mem record⟩
  obtain ⟨_, _, source, _, _, _, _, _, trace⟩ := marked
  have all := list_all_of_last_and_backward (P := fun factor => ∃ ss, (factor, ss) ∈ rec) lastFactor lastRecord (by
    intro upper lower pair lowerRecord
    obtain ⟨upperRow, upperAt, _, upperE⟩ :=
      currentPlusOne_all_endpoints currentReal.valid trace guard upper lower pair
    obtain ⟨ss, member⟩ := lowerRecord
    exact propagation upper (List.of_mem_zip pair).1 (rowAt_bounds upperAt).1
      upperRow lower ss upperAt upperE member)
  intro actual actualComputed
  have same : actual = word := Option.some.inj (actualComputed.symm.trans computed)
  simpa only [same] using all

/-- The first parallel trace no longer needs an all-factor-record assumption. -/
theorem scanRankReach_completion_first_trace {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    {sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization initial initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (transport : ScanPriorEndpointTransport initial initialTheta initialEmbedding r)
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources) :
    ∃ word x, computeMarkTrace a r y = some word ∧ sources.getLast? = some x ∧
      Trace a x (y + 1) (word.dropLast.map (fun i => i + 1) ++ [x]) := by
  exact completionRecord_first_parallel_trace
    (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) currentReal.valid historyValid hr hm hc
    (scanRankReach_completion_all_factor_records reach entryReal currentReal geometry transport hr hm hc)
end FullMarkedBLP


