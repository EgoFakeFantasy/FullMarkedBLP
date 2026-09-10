import FullMarkedBLP.NativeBirthSegment
import FullMarkedBLP.NativeFirstTargetSegment
import FullMarkedBLP.NativeTargetParallelEdge

namespace FullMarkedBLP

/-- Exact first-target entry at a real scan birth determines both packet width
and every parallel predecessor. The endpoint need not be adjacent to the top. -/
theorem native_birth_exact_packet_of_first_target {lambda : Ordinal.{u}} {initial a b : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records}
    {r base e top : Nat} {lowerSources sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (h : RankRowRealization a theta embedding)
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    {row : Row} (hr : rowAt a r = some row) (hp : row.p = some base) (he : row.e = some e)
    (record : (base, lowerSources) ∈ rec)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (birth : native (completeFrozenMarks a rec r) r = some (b, sources))
    (nonempty : sources ≠ []) (positive : 0 < top) (size : top ≤ lowerSources.length)
    (first : (rowAt (completeFrozenMarks a rec r) e).bind Row.b = some (base + top)) :
    sources.length = top ∧ ∀ k, 0 < k → k ≤ top →
      base + k ∈ sources ∧ predecessor b (r + k) = some (base + k) := by
  obtain ⟨mid, atMid, _⟩ := Option.bind_eq_some_iff.mp birth
  have midEndpoint := scanRankReach_completed_e_above_predecessor_block reach h historyValid
    hr hp he record events atMid
  obtain ⟨valid, fixed⟩ := completeFrozenMarks_event_geometry hr h.valid events
  have midP : mid.p = some base := by
    have eq := fixed r
    simpa only [predecessor, atMid, hr, Option.bind_some, hp] using eq
  have pred : predecessor (completeFrozenMarks a rec r) r = some base := by
    simp only [predecessor, atMid, Option.bind_some, midP]
  have source := native_sources_of_success birth
  have walk := nativeSources_nonempty_fuel atMid midP midEndpoint.1 source nonempty
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have targetBound := scanReach_record_targets_before plain record
  have chain : ∀ k, 0 < k → k ≤ top →
      (rowAt (completeFrozenMarks a rec r) (base + k)).bind Row.b = some (base + k - 1) := by
    intro k hk hkt
    rw [completeFrozenMarks_other_row (by omega : base + k ≠ r)]
    exact scanReach_record_target_b plain historyValid record hk (by omega)
  obtain ⟨length, members⟩ := nativeSourcesFuel_exact_length_of_first_target valid walk first positive chain
  refine ⟨length, ?_⟩
  intro k hk hkt
  exact ⟨members k hk hkt,
    native_target_segment_predecessor valid birth pred (members top positive (Nat.le_refl _)) chain hk hkt⟩

end FullMarkedBLP
