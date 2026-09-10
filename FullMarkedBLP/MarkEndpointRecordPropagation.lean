import FullMarkedBLP.OriginMapComparison

namespace FullMarkedBLP

/-- Actual original mark factors inherit record existence from their +1 child. -/
theorem scanRankReach_mark_endpoint_record_propagation {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization initial initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (transport : ScanPriorEndpointTransport initial initialTheta initialEmbedding r)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks) :
    ∃ word, MarkTrace a r y word ∧ computeMarkTrace a r y = some word ∧
      ∀ factor ∈ word.dropLast, 0 < factor →
        ∀ current lower ss, rowAt a factor = some current → current.e = some (lower + 1) →
          (lower, ss) ∈ rec → ∃ upperSources, (factor, upperSources) ∈ rec := by
  obtain ⟨psi, original, entry, psiMono, psiZero, psiOwner, atEntry, _, psiHolds, _, members, traces⟩ :=
    scanRankReach_current_mark_origins reach hr
  obtain ⟨v, vm, vy⟩ := (members y).mp hm
  obtain ⟨k, source, xs, delta, hk, hv, hs, oldTrace, _, _⟩ := entryReal.marked original entry v atEntry vm
  have oldMarked : MarkTrace initial original v xs :=
    ⟨entry, k, source, atEntry, vm, hk, hv, hs, oldTrace⟩
  have marked : MarkTrace a r y (xs.map psi) := by
    simpa only [vy] using traces geometry v xs oldMarked
  obtain ⟨phi, originalIndex, mono, _, _, maximum, lengths, holds, tail, _, endpoints, aligned⟩ :=
    scanRankReach_endpoint_alignment reach
  refine ⟨xs.map psi, marked, computeMarkTrace_complete currentReal.valid marked, ?_⟩
  intro factor mem positive current lower ss atCurrent endpoint lowerMem
  have inWord := (List.dropLast_sublist (xs.map psi)).subset mem
  obtain ⟨j, jm, jf⟩ := List.mem_map.mp inWord
  have jv := trace_member_le_head entryReal.valid oldTrace jm
  have voriginal := ((entryReal.proper original entry atEntry).2 v vm).1
  have originalBound := rowAt_bounds atEntry
  have currentBound := rowAt_bounds hr
  have phiBound := origin_map_bounded mono maximum lengths tail (j := j) (by omega)
  have psiBound : psi j ≤ a.length + 1 := by
    have le := psiMono.monotone (show j ≤ original by omega)
    omega
  have same : phi j = psi j := realized_column_index_eq currentReal phiBound psiBound
    ((holds j).1.trans (psiHolds j).1.symm)
  have jpositive : 0 < j := by
    by_contra no
    have zero : j = 0 := by omega
    simp only [zero, psiZero] at jf
    omega
  obtain ⟨originalRow, atOriginal⟩ := rowAt_exists (a := initial) jpositive (by omega)
  by_contra missing
  have noRecord : ∀ upperSources, (phi j, upperSources) ∉ rec := by
    intro upperSources member
    exact missing ⟨upperSources, by simpa only [same, jf] using member⟩
  have valid := entryReal.valid j originalRow atOriginal
  have room := Row.step_lt_length valid.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := originalRow.core) (k := originalRow.step)
    valid.2.2.2.1 (by omega)
  have mapped := endpoints transport j e (by simpa only [atOriginal, Option.bind_some] using he) noRecord
  have equal : phi e = lower + 1 := by
    rw [same, jf, atCurrent] at mapped
    simpa only [Option.bind_some, endpoint, Option.some.injEq] using mapped.symm
  obtain ⟨index, _, _, left, right⟩ := aligned lower ss lowerMem
  have nonempty : ss ≠ [] :=
    ((scanReach_records_before (scanEmbeddingReach_forget (scanRankReach_embeddings reach))).2
      (lower, ss) lowerMem).2.2
  exact historical_image_ne_first_target mono left right (List.length_pos_iff.mpr nonempty) e equal

end FullMarkedBLP
