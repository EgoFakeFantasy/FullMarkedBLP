import FullMarkedBLP.FrozenRecordDecision
import FullMarkedBLP.PacketAllEndpoints

namespace FullMarkedBLP

/-- Actual guarded internal edges and their source-successor rows are in the
copied region. This is a geometric input, not the full recorded Sat invariant. -/
theorem shortCopy_frozen_internal_endpoints {lambda : Ordinal.{u}}
    {parent copied a : Pattern} {rec : Records} {r y : Nat}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (parentValid : ∀ i rw, rowAt parent i = some rw → rw.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanReach copied a rec r) (h : RankRowRealization a theta embedding)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row : Row} {sources : List Nat} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∃ xs, MarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y xs ∧
      ∀ upper lower, (upper, lower) ∈ xs.dropLast.zip xs.dropLast.tail →
        parent.length ≤ upper ∧ parent.length ≤ lower + 1 ∧
        ∃ factorRow endpointRow v,
          rowAt (processed.foldl (fun current z => completeMark current rec r z) a) upper = some factorRow ∧
          factorRow.p = some lower ∧ factorRow.e = some (lower + 1) ∧
          rowAt (processed.foldl (fun current z => completeMark current rec r z) a) (lower + 1) = some endpointRow ∧
          endpointRow.b = some v ∧ v ≤ lower := by
  obtain ⟨xs, mark, region⟩ := shortCopy_frozen_completion_factor_region parentValid sat copy reach h processed events hr hm hc
  have valid := frozen_fold_coreValid processed h.valid events
  have computed := computeMarkTrace_complete valid mark
  obtain ⟨word, terminal, currentComputed, _, _, _, guard⟩ := completionRecord_iff.mp hc
  have eq := Option.some.inj (currentComputed.symm.trans computed)
  subst word
  have markCopy := mark
  obtain ⟨_, _, source, _, _, _, _, _, trace⟩ := markCopy
  refine ⟨xs, mark, ?_⟩
  intro upper lower pair
  obtain ⟨factorRow, factorAt, hp, he⟩ := currentPlusOne_all_endpoints valid trace guard upper lower pair
  obtain ⟨endpointRow, v, endpointAt, hb, bound⟩ := currentPlusOne_all_endpoint_b_bounds valid trace guard upper lower pair
  have upperBound := region upper (List.of_mem_zip pair).1
  have lowerBound := region lower (List.mem_of_mem_tail (List.of_mem_zip pair).2)
  exact ⟨upperBound, by omega, factorRow, endpointRow, v, factorAt, hp, he, endpointAt, hb, bound⟩

end FullMarkedBLP
