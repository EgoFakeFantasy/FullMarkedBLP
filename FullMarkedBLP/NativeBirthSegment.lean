import FullMarkedBLP.NativeEntranceAboveRecord
import FullMarkedBLP.NativePathEntry
import FullMarkedBLP.ScanRecordedTargetB
import FullMarkedBLP.NativeBottomSat

namespace FullMarkedBLP

/-- At a real birth, the guarded bottom endpoint and lower record supply all
segment-entry inputs except the path-local no-jump condition. -/
theorem native_birth_full_segment_of_path_no_jump {lambda : Ordinal.{u}} {initial a b : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records}
    {r base e top : Nat} {lowerSources sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (h : RankRowRealization a theta embedding)
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    {row bottom : Row} (hr : rowAt a r = some row) (hp : row.p = some base) (he : row.e = some e)
    (record : (base, lowerSources) ∈ rec)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (birth : native (completeFrozenMarks a rec r) r = some (b, sources))
    (nonempty : sources ≠ []) (atBottom : rowAt b r = some bottom)
    (bottomE : bottom.e = some (base + 1)) (positive : 0 < top) (size : top ≤ lowerSources.length)
    (noJump : ∀ z next, z ∈ e :: sources → base + top < z →
      (rowAt (completeFrozenMarks a rec r) z).bind Row.b = some next →
      next ≤ base ∨ base + top ≤ next) :
    ∀ k, 0 < k → k ≤ top → base + k ∈ sources := by
  obtain ⟨mid, atMid, _⟩ := Option.bind_eq_some_iff.mp birth
  have midEndpoint := scanRankReach_completed_e_above_predecessor_block reach h historyValid
    hr hp he record events atMid
  obtain ⟨valid, fixed⟩ := completeFrozenMarks_event_geometry hr h.valid events
  have midP : mid.p = some base := by
    have eq := fixed r
    simpa only [predecessor, atMid, hr, Option.bind_some, hp] using eq
  have source := native_sources_of_success birth
  have walk := nativeSources_nonempty_fuel atMid midP midEndpoint.1 source nonempty
  have length : 0 < sources.length := List.length_pos_iff.mpr nonempty
  obtain ⟨last, lastAt⟩ := fromRight_exists (xs := sources) (k := 1) (by decide) (by omega)
  have lastSource : sources.getLast? = some last := by
    simpa [fromRight, show 1 ≤ sources.length by omega, List.getLast?_eq_getElem?] using lastAt
  obtain ⟨actualBottom, _, _, actualAt, _, actualE, _⟩ :=
    native_bottom_sat_witness valid atMid midP midEndpoint.1 source lastSource birth
  have same : actualBottom = bottom := Option.some.inj (actualAt.symm.trans atBottom)
  have lastEq : last = base + 1 := by
    rw [same] at actualE
    exact Option.some.inj (actualE.symm.trans bottomE)
  have reaches : base + 1 ∈ sources := by
    simpa only [lastEq] using List.mem_of_getLast? lastSource
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have targetBound := scanReach_record_targets_before plain record
  have chain : ∀ k, 0 < k → k ≤ top →
      (rowAt (completeFrozenMarks a rec r) (base + k)).bind Row.b = some (base + k - 1) := by
    intro k hk hkt
    rw [completeFrozenMarks_other_row (by omega : base + k ≠ r)]
    exact scanReach_record_target_b plain historyValid record hk (by omega)
  exact nativeSourcesFuel_full_segment_of_path_no_jump walk (by have := midEndpoint.2; omega)
    positive reaches noJump chain

end FullMarkedBLP
