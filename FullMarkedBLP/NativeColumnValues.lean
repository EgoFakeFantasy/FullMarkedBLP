import FullMarkedBLP.NativeCertificateShift

namespace FullMarkedBLP

/-- Insert t new column values immediately after column r. -/
def nativeColumnValues {alpha : Type u} (old fresh : Nat → alpha) (r t x : Nat) : alpha :=
  if x ≤ r then old x else if x ≤ r + t then fresh (x - r - 1) else old (x - t)

theorem nativeColumnValues_preserves {alpha : Type u} (old fresh : Nat → alpha)
    (r t i : Nat) : nativeColumnValues old fresh r t (shiftAfter r t i) = old i := by
  unfold nativeColumnValues shiftAfter
  split <;> rename_i h
  · rw [if_neg (by omega), if_neg (by omega)]
    congr 1
    omega
  · rw [if_pos (by omega)]

theorem nativeColumnValues_inserted {alpha : Type u} (old fresh : Nat → alpha)
    (r t k : Nat) (hk : k < t) :
    nativeColumnValues old fresh r t (r + 1 + k) = fresh k := by
  unfold nativeColumnValues
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

/-- Only the first inserted value needs an upper bound for old-word successor
comparison. All other shifted successors are exactly old column values. -/
theorem nativeColumnValues_successor_le {alpha : Type u} [Preorder alpha]
    (old fresh : Nat → alpha) (r t v : Nat)
    (hfirst : 0 < t → fresh 0 ≤ old (r + 1)) :
    nativeColumnValues old fresh r t (shiftAfter r t v + 1) ≤ old (v + 1) := by
  by_cases hv : v = r
  · subst v
    by_cases ht : t = 0
    · subst t
      simp [nativeColumnValues, shiftAfter]
    · have he := nativeColumnValues_inserted old fresh r t 0 (by omega)
      simp only [Nat.add_zero] at he
      simpa only [shiftAfter, Nat.lt_irrefl, if_false, he] using hfirst (by omega)
  · have he : shiftAfter r t v + 1 = shiftAfter r t (v + 1) := by
      unfold shiftAfter
      split <;> split <;> omega
    rw [he, nativeColumnValues_preserves]

/-- The concrete insertion definitions discharge old factor and column
preservation; certificate transport needs only the first new column bound. -/
theorem rankCertificate_native_values {lambda : Ordinal.{u}}
    (oldEmbedding freshEmbedding : Nat → RankElementaryEmbedding lambda)
    (oldTheta freshTheta : Nat → OrdinalDomain lambda) (r t : Nat) (word : List Nat)
    (owner : RankElementaryEmbedding lambda)
    (hfirst : 0 < t → freshTheta 0 ≤ oldTheta (r + 1))
    {oldDelta newDelta : OrdinalDomain lambda}
    (ho : naturalCutoff (fun i => rankOrdinalAction (oldEmbedding i)) oldTheta word = some oldDelta)
    (hn : naturalCutoff
      (fun i => rankOrdinalAction (nativeColumnValues oldEmbedding freshEmbedding r t i))
      (nativeColumnValues oldTheta freshTheta r t) (word.map (shiftAfter r t)) = some newDelta)
    (certificate : rankCutoffAgreement oldDelta.val owner
      (evalWord (fun i => (oldEmbedding i : RankDomain lambda → RankDomain lambda)) word)) :
    rankCutoffAgreement newDelta.val owner
      (evalWord (fun i => ((nativeColumnValues oldEmbedding freshEmbedding r t i : RankElementaryEmbedding lambda) :
        RankDomain lambda → RankDomain lambda)) (word.map (shiftAfter r t))) := by
  exact rankCertificate_reindex oldEmbedding (nativeColumnValues oldEmbedding freshEmbedding r t)
    oldTheta (nativeColumnValues oldTheta freshTheta r t) (shiftAfter r t) word owner
    (fun v _ => nativeColumnValues_preserves oldEmbedding freshEmbedding r t v)
    (fun v _ => nativeColumnValues_successor_le oldTheta freshTheta r t v hfirst)
    ho hn certificate
end FullMarkedBLP


