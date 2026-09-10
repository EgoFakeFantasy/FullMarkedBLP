import FullMarkedBLP.VerifiedScanObligations

namespace FullMarkedBLP

/-- Original Sat-style B bounds give a concrete cap at the end of the lower
record block, under the same map as the untouched future rows. -/
theorem scanRankReach_original_endpoint_caps {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization initial initialTheta initialEmbedding)
    (verified : ScanPriorVerifiedEvents initial initialTheta initialEmbedding r) :
    ∃ (phi : Nat → Nat) (original : Nat), StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ k, phi (original + k) = r + k) ∧
      (∀ owner row, original ≤ owner → rowAt initial owner = some row →
        rowAt a (phi owner) = some ⟨row.core.map phi, row.step, row.marks.map phi⟩) ∧
      ∀ e er v lower ss, rowAt initial e = some er → er.b = some v → v ≤ lower →
        (phi lower, ss) ∈ rec →
        ∃ w, (rowAt a (phi e)).bind Row.b = some w ∧ w ≤ phi lower + ss.length := by
  obtain ⟨phi, original, mono, zero, _, holds, tail, rows, records, intervals⟩ :=
    scanRankReach_original_b_intervals reach entryReal
  have bands := intervals (scanPriorVerifiedEvents_geometry verified)
    (scanPriorVerifiedEvents_endpoint_transport verified) verified
  refine ⟨phi, original, mono, zero, holds, tail, rows, ?_⟩
  intro e er v lower ss atE atB bound record
  obtain ⟨w, actual, _, upper⟩ := bands e er v atE atB
  obtain ⟨i, _, base, successor⟩ := records (phi lower) ss record
  have same : i = lower := mono.injective base
  subst i
  have cap : phi (v + 1) ≤ phi (lower + 1) := mono.monotone (by omega)
  rw [successor] at cap
  exact ⟨w, actual, by omega⟩

end FullMarkedBLP
