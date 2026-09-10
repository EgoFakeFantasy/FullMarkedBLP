import FullMarkedBLP.ScanFutureMarkedOrigins

namespace FullMarkedBLP

/-- Every mark on the current unprocessed row has an entry-row origin under
the same semantic map that transports its marked traces. -/
theorem scanRankReach_current_mark_origins {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    {current : Row} (hr : rowAt a r = some current) :
    ∃ (phi : Nat → Nat) (original : Nat) (entry : Row),
      StrictMono phi ∧ phi 0 = 0 ∧ phi original = r ∧
      rowAt initial original = some entry ∧
      current = ⟨entry.core.map phi, entry.step, entry.marks.map phi⟩ ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, i < original ∧ phi i = terminal ∧ phi (i + 1) = terminal + sources.length + 1) ∧
      (∀ y, y ∈ current.marks ↔ ∃ v ∈ entry.marks, phi v = y) ∧
      (ScanPriorGeometry initial initialTheta initialEmbedding r →
        ∀ v xs, MarkTrace initial original v xs → MarkTrace a r (phi v) (xs.map phi)) := by
  obtain ⟨phi, original, hmono, hzero, hlen, holds, tail, rows, marks, records⟩ :=
    scanRankReach_future_markTraces h
  have mapped : phi original = r := by simpa using tail 0
  have rb := rowAt_bounds hr
  have positive : 0 < original := by
    by_contra hn
    have he : original = 0 := by omega
    rw [he, hzero] at mapped
    omega
  obtain ⟨entry, he⟩ := rowAt_exists (a := initial) positive (by omega : original ≤ initial.length)
  have roweq := rows original entry (Nat.le_refl _) he
  rw [mapped, hr] at roweq
  have shape := Option.some.inj roweq
  refine ⟨phi, original, entry, hmono, hzero, mapped, he, shape, holds, records, ?_, ?_⟩
  · intro y
    rw [shape]
    exact List.mem_map
  · intro geometry v xs ht
    simpa only [mapped] using marks geometry original v xs (Nat.le_refl _) ht

end FullMarkedBLP


