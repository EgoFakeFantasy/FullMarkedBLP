import FullMarkedBLP.ScanOriginAlignment

namespace FullMarkedBLP

/-- The unscanned tail retains its original ordinal values and embeddings.
The original cursor counts consumed rows, independently of inserted blocks. -/
theorem scanRankReach_original_tail {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ∃ original, 1 ≤ original ∧ original ≤ initial.length + 1 ∧
      initial.length + r = a.length + original ∧
      ∀ k, theta (r + k) = initialTheta (original + k) ∧
        embedding (r + k) = initialEmbedding (original + k) := by
  obtain ⟨phi, original, _, _, hp, hmax, hlen, holds, tail, _, _⟩ := scanRankReach_origin_alignment h
  refine ⟨original, hp, hmax, hlen, ?_⟩
  intro k
  rw [← tail k]
  exact holds (original + k)
/-- A record's birth successor is an entry of the scan's original column
sequence, with an index determined by the birth cursor and pattern length. -/
theorem scanRankReach_record_original_successor {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) :
    ∃ before history oldTheta oldEmbedding after original,
      ScanRankReach initial initialTheta initialEmbedding before history terminal oldTheta oldEmbedding ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) ∧
      1 ≤ original ∧ original ≤ initial.length ∧
      initial.length + terminal = before.length + original ∧
      oldTheta (terminal + 1) = initialTheta (original + 1) ∧
      embedding terminal = initialEmbedding original := by
  obtain ⟨before, history, oldTheta, oldEmbedding, after, reach, hn, he, _, _⟩ :=
    scanRankReach_record_birth h hm
  obtain ⟨original, hp, hmax, hlen, tail⟩ := scanRankReach_original_tail reach
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  have hbound := (rowAt_bounds hr).2
  rw [completeFrozenMarks_length] at hbound
  refine ⟨before, history, oldTheta, oldEmbedding, after, original, reach, hn,
    hp, by omega, hlen, (tail 1).1, ?_⟩
  rw [he]
  simpa only [Nat.add_zero] using (tail 0).2

end FullMarkedBLP


