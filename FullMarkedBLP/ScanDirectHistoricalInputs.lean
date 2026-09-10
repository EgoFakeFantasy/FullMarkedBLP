import FullMarkedBLP.ScanOriginalMap

namespace FullMarkedBLP

/-- The same origin map transports a direct saved certificate and identifies
its record's endpoint successor with the original natural cutoff column. -/
theorem scanRankReach_direct_historical_inputs {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      ∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, 1 ≤ i ∧ i ≤ initial.length ∧ phi i = terminal ∧
          theta (terminal + sources.length + 1) = initialTheta (i + 1) ∧
          ∀ owner delta,
            rankCutoffAgreement delta (initialEmbedding owner) (initialEmbedding i) →
            (initialTheta (i + 1)).val ≤ delta →
            rankCutoffAgreement delta (embedding (phi owner)) (embedding terminal) ∧
            (theta (terminal + sources.length + 1)).val ≤ delta := by
  obtain ⟨phi, original, hmono, hzero, _, hmax, _, holds, _, _, records⟩ :=
    scanRankReach_origin_alignment h
  refine ⟨phi, hmono, hzero, holds, ?_⟩
  intro terminal sources hm
  obtain ⟨i, hi, hib, he, hn⟩ := records terminal sources hm
  have endpoint : theta (terminal + sources.length + 1) = initialTheta (i + 1) := by
    rw [← hn]
    exact (holds (i + 1)).1
  refine ⟨i, hi, by omega, he, endpoint, ?_⟩
  intro owner delta saved covered
  constructor
  · rw [← he, (holds owner).2, (holds i).2]
    exact saved
  · simpa only [endpoint] using covered

/-- The current cursor and each record are aligned simultaneously. An entry
certificate at the original direct natural cutoff supplies both required
historical inputs for that actual current owner. -/
theorem scanRankReach_current_direct_history {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ∃ original, 1 ≤ original ∧ original ≤ initial.length + 1 ∧
      embedding r = initialEmbedding original ∧
      ∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, 1 ≤ i ∧ i < original ∧
          embedding terminal = initialEmbedding i ∧
          theta (terminal + sources.length + 1) = initialTheta (i + 1) ∧
          (rankCutoffAgreement (initialTheta (i + 1)).val
              (initialEmbedding original) (initialEmbedding i) →
            rankCutoffAgreement (initialTheta (i + 1)).val (embedding r) (embedding terminal)) := by
  obtain ⟨phi, original, _, _, hp, hmax, _, holds, tail, _, records⟩ :=
    scanRankReach_origin_alignment h
  have current : embedding r = initialEmbedding original := by
    have ht : phi original = r := by simpa using tail 0
    rw [← ht]
    exact (holds original).2
  refine ⟨original, hp, hmax, current, ?_⟩
  intro terminal sources hm
  obtain ⟨i, hi, hib, he, hn⟩ := records terminal sources hm
  have factor : embedding terminal = initialEmbedding i := by rw [← he]; exact (holds i).2
  refine ⟨i, hi, hib, factor, ?_, ?_⟩
  · rw [← hn]
    exact (holds (i + 1)).1
  · simpa only [current, factor] using (fun h => h)

end FullMarkedBLP

