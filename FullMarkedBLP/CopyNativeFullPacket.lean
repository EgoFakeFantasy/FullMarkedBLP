import FullMarkedBLP.CopyOwnerEndpointBoundary

namespace FullMarkedBLP

/-- Every nonempty native birth with a retained predecessor after a Sat short
copy creates the entire predecessor block as its source segment. Its
width equals the predecessor record length. -/
theorem shortCopy_native_birth_full_packet {lambda : Ordinal.{u}} {parent copied a b : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r base e : Nat}
    {lowerSources sources : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    {row : Row} (hr : rowAt a r = some row) (hp : row.p = some base) (he : row.e = some e)
    (record : (base, lowerSources) ∈ rec)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (birth : native (completeFrozenMarks a rec r) r = some (b, sources)) (nonempty : sources ≠ []) :
    sources.length = lowerSources.length ∧ ∀ k, 0 < k → k ≤ lowerSources.length →
      base + k ∈ sources ∧ predecessor b (r + k) = some (base + k) := by
  have geometry := scanPriorVerifiedEvents_geometry verified
  have historyValid : ∀ before history owner, ScanReach copied before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i := by
    intro before history owner reached earlier
    obtain ⟨oldTheta, oldEmbedding, labelled⟩ := scanReach_rank_lift reached initialTheta initialEmbedding
    exact (geometry before history owner oldTheta oldEmbedding labelled earlier).1
  obtain ⟨mid, atMid, _⟩ := Option.bind_eq_some_iff.mp birth
  obtain ⟨valid, fixed⟩ := completeFrozenMarks_event_geometry hr currentReal.valid events
  have source := native_sources_of_success birth
  have eligible := (completeFrozenMarks_eligible_iff hr events atMid).mp
    (nativeSources_nonempty_eligible atMid source nonempty)
  have midP : mid.p = some base := by
    have eq := fixed r
    simpa only [predecessor, atMid, hr, Option.bind_some, hp] using eq
  have midE := completeFrozenMarks_preserves_e historyValid
    (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) currentReal hr he events atMid
  have step : 1 < mid.step :=
    nativeSources_nonempty_step_ge_two (valid r mid atMid) atMid source nonempty
  have endpointBelow := fromRight_lt_last (valid r mid atMid).1 (valid r mid atMid).2.2.1 step midE
  obtain ⟨w, currentB, cap⟩ := shortCopy_scan_owner_endpoint_boundary parentValid sat copy reach entryReal
    currentReal verified hr hp he eligible record
  have firstB : (rowAt (completeFrozenMarks a rec r) e).bind Row.b = some w := by
    rw [completeFrozenMarks_other_row (by omega : e ≠ r)]
    exact currentB
  cases sources with
  | nil => contradiction
  | cons head tail =>
    obtain ⟨er, erAt, erB⟩ := nativeSources_head_b atMid midP midE source
    have eq : head = w := by
      simpa only [erAt, Option.bind_some, erB, Option.some.injEq] using firstB
    have bounds := nativeSources_between valid atMid midP midE source head (List.mem_cons_self)
    have full : head = base + lowerSources.length := by
      rcases cap with small | top
      · omega
      · omega
    have first : (rowAt (completeFrozenMarks a rec r) e).bind Row.b = some (base + lowerSources.length) := by
      simpa only [← eq, full] using firstB
    exact native_birth_exact_packet_of_first_target reach currentReal historyValid
      hr hp he record events birth nonempty (by omega : 0 < lowerSources.length) (Nat.le_refl _) first

end FullMarkedBLP
