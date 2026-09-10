import FullMarkedBLP.RecordedEmbeddingInvariant

namespace FullMarkedBLP

theorem recordedEmbeddingsAgree_scan_step {lambda : Ordinal.{u}} {initial a : Pattern}
    {rec : Records} {r : Nat} (reach : ScanReach initial a rec r)
    (embedding : Nat → RankElementaryEmbedding lambda) (h : RecordedEmbeddingsAgree embedding rec)
    (sources : List Nat) :
    RecordedEmbeddingsAgree (nativeEmbeddingValues embedding r sources.length)
      (if sources.isEmpty then rec else (r, sources) :: rec) := by
  by_cases hs : sources = []
  · subst sources
    simpa only [List.isEmpty_nil, if_true, List.length_nil, nativeEmbeddingValues,
      nativeColumnValues_zero] using h
  · simp only [List.isEmpty_iff, hs, if_false]
    exact recordedEmbeddingsAgree_native_step embedding h
      (fun terminal ss hm => scanReach_record_targets_before reach hm) sources

end FullMarkedBLP
