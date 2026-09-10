import FullMarkedBLP.ScanOriginAlignment

namespace FullMarkedBLP

/-- One coherent increasing map tracks every original column and owner through
the complete scan history, including all intermediate native insertions. -/
theorem scanRankReach_original_map {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      ∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i := by
  obtain ⟨phi, original, hmono, hzero, _, _, _, holds, _, _, _⟩ := scanRankReach_origin_alignment h
  exact ⟨phi, hmono, hzero, holds⟩
/-- All entry weak certificates survive at their original historical cutoffs
under the same map. This does not identify current computed mark traces. -/
theorem scanRankReach_entry_certificates {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, 1 ≤ i ∧ i ≤ initial.length ∧ phi i = terminal ∧ phi (i + 1) = terminal + sources.length + 1) ∧
      ∀ owner word delta,
        rankCutoffAgreement delta (initialEmbedding owner)
          (evalWord (fun i => (initialEmbedding i : RankDomain lambda → RankDomain lambda)) word) →
        rankCutoffAgreement delta (embedding (phi owner))
          (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) (word.map phi)) := by
  obtain ⟨phi, original, hmono, hzero, _, hmax, _, holds, _, _, records⟩ :=
    scanRankReach_origin_alignment h
  have aligned : ∀ terminal sources, (terminal, sources) ∈ rec →
      ∃ i, 1 ≤ i ∧ i ≤ initial.length ∧ phi i = terminal ∧ phi (i + 1) = terminal + sources.length + 1 := by
    intro terminal sources hm
    obtain ⟨i, hi, hib, he, hn⟩ := records terminal sources hm
    exact ⟨i, hi, by omega, he, hn⟩
  refine ⟨phi, hmono, hzero, holds, aligned, ?_⟩
  intro owner word delta hc
  rw [(holds owner).2]
  intro x z hx hz
  have he := evalWord_reindex
    (fun i => (initialEmbedding i : RankDomain lambda → RankDomain lambda))
    (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) phi word
    (fun i _ => by dsimp only; rw [(holds i).2]) z
  rw [he]
  exact hc x z hx hz

end FullMarkedBLP




