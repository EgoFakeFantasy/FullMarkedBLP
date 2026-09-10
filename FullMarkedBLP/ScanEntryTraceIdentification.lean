import FullMarkedBLP.ScanOriginAlignment

namespace FullMarkedBLP

/-- Under prior local predecessor preservation, entry traces are the exact
computed traces at mapped endpoints, under the same record-aligned map. -/
theorem scanRankReach_entry_trace_identification {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, 1 ≤ i ∧ i ≤ initial.length ∧ phi i = terminal ∧
          phi (i + 1) = terminal + sources.length + 1) ∧
      ∀ s y xs, Trace initial s y xs →
        Trace a (phi s) (phi y) (xs.map phi) ∧
        ∀ fuel ys, traceFuel a (phi s) fuel (phi y) = some ys → ys = xs.map phi := by
  obtain ⟨phi, original, hmono, hzero, _, hmax, _, holds, _, predecessors, records⟩ :=
    scanRankReach_origin_alignment h
  refine ⟨phi, hmono, hzero, holds, ?_, ?_⟩
  · intro terminal sources hm
    obtain ⟨i, hi, hib, he, hn⟩ := records terminal sources hm
    exact ⟨i, hi, by omega, he, hn⟩
  · intro s y xs ht
    have transported := trace_map phi (fun hxy => hmono hxy) ht
      (fun x z _ hp => predecessors geometry x z hp)
    exact ⟨transported, fun _ _ hc => trace_unique (traceFuel_sound hc) transported⟩

end FullMarkedBLP

