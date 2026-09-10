import FullMarkedBLP.CompletionExactCertificate

namespace FullMarkedBLP

theorem native_preserves_historical_agreement {lambda delta : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (r t owner : Nat) (word : List Nat)
    (hc : rankCutoffAgreement delta (embedding owner)
      (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) word)) :
    rankCutoffAgreement delta
      (nativeEmbeddingValues embedding r t (shiftAfter r t owner))
      (evalWord (fun i => (nativeEmbeddingValues embedding r t i : RankDomain lambda → RankDomain lambda))
        (word.map (shiftAfter r t))) := by
  rw [nativeEmbeddingValues_old]
  intro x z hx hz
  have he := evalWord_reindex
    (fun i => (embedding i : RankDomain lambda → RankDomain lambda))
    (fun i => (nativeEmbeddingValues embedding r t i : RankDomain lambda → RankDomain lambda))
    (shiftAfter r t) word (fun i _ => by dsimp only; rw [nativeEmbeddingValues_old]) z
  rw [he]
  exact hc x z hx hz

end FullMarkedBLP

