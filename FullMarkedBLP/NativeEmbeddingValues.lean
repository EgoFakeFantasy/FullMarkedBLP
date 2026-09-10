import FullMarkedBLP.NativeBottomEndpointRealization

namespace FullMarkedBLP

/-- Candidate native block interpretation: repeat the old owner embedding
through the inserted block, retaining every shifted old embedding. -/
noncomputable def nativeEmbeddingValues {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (r t : Nat) :
    Nat → RankElementaryEmbedding lambda :=
  nativeColumnValues embedding (fun _ => embedding r) r t

theorem nativeEmbeddingValues_block {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (r t k : Nat) (hk : k ≤ t) :
    nativeEmbeddingValues embedding r t (r + k) = embedding r := by
  unfold nativeEmbeddingValues nativeColumnValues
  by_cases hz : k = 0
  · subst k; simp
  · rw [if_neg (by omega), if_pos (by omega)]

theorem nativeEmbeddingValues_old {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (r t i : Nat) :
    nativeEmbeddingValues embedding r t (shiftAfter r t i) = embedding i :=
  nativeColumnValues_preserves embedding (fun _ => embedding r) r t i

/-- A block direct mark's singleton factor has exactly the owner's embedding,
so its weak certificate holds at every rank cutoff. Actual direct MarkTrace
and all new block edges must still be established separately. -/
theorem nativeEmbeddingValues_direct_certificate {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (r t i j : Nat)
    (hi : i ≤ t) (hj : j ≤ t) (delta : Ordinal.{u}) :
    rankCutoffAgreement delta (nativeEmbeddingValues embedding r t (r + i))
      (evalWord (fun v => (nativeEmbeddingValues embedding r t v :
        RankDomain lambda → RankDomain lambda)) [r + j]) := by
  intro x z hx hz
  simp only [evalWord, nativeEmbeddingValues_block embedding r t i hi,
    nativeEmbeddingValues_block embedding r t j hj]

end FullMarkedBLP
