import FullMarkedBLP.RankCertificateReindex

namespace FullMarkedBLP

/-- The native insertion can create a gap after the old owner, but never
places the new successor to the right of the shifted old successor. -/
theorem shiftAfter_successor_le (r t v : Nat) :
    shiftAfter r t v + 1 ≤ shiftAfter r t (v + 1) := by
  have hs := shiftAfter_strict r t (show v < v + 1 by omega)
  omega

theorem native_successor_column_le {alpha : Type u} [Preorder alpha]
    (oldTheta newTheta : Nat → alpha) (r t bound v : Nat)
    (hv : v + 1 ≤ bound)
    (preserved : ∀ i, i ≤ bound → newTheta (shiftAfter r t i) = oldTheta i)
    (increasing : ∀ i j, i ≤ j → j ≤ bound + t → newTheta i ≤ newTheta j) :
    newTheta (shiftAfter r t v + 1) ≤ oldTheta (v + 1) := by
  rw [← preserved (v + 1) hv]
  apply increasing _ _ (shiftAfter_successor_le r t v)
  unfold shiftAfter
  split <;> omega

/-- Certificate transport specialized to the literal native column map.
The semantic construction still owes preservation of factor embeddings and
old columns, and monotonicity of the newly inserted columns. -/
theorem rankCertificate_native_shift {lambda : Ordinal.{u}}
    (oldEmbedding newEmbedding : Nat → RankElementaryEmbedding lambda)
    (oldTheta newTheta : Nat → OrdinalDomain lambda) (r t bound : Nat) (word : List Nat)
    (owner : RankElementaryEmbedding lambda)
    (factors : ∀ v ∈ word, newEmbedding (shiftAfter r t v) = oldEmbedding v)
    (wordBound : ∀ v ∈ word, v + 1 ≤ bound)
    (preserved : ∀ i, i ≤ bound → newTheta (shiftAfter r t i) = oldTheta i)
    (increasing : ∀ i j, i ≤ j → j ≤ bound + t → newTheta i ≤ newTheta j)
    {oldDelta newDelta : OrdinalDomain lambda}
    (ho : naturalCutoff (fun i => rankOrdinalAction (oldEmbedding i)) oldTheta word = some oldDelta)
    (hn : naturalCutoff (fun i => rankOrdinalAction (newEmbedding i)) newTheta
      (word.map (shiftAfter r t)) = some newDelta)
    (certificate : rankCutoffAgreement oldDelta.val owner
      (evalWord (fun i => (oldEmbedding i : RankDomain lambda → RankDomain lambda)) word)) :
    rankCutoffAgreement newDelta.val owner
      (evalWord (fun i => (newEmbedding i : RankDomain lambda → RankDomain lambda))
        (word.map (shiftAfter r t))) := by
  exact rankCertificate_reindex oldEmbedding newEmbedding oldTheta newTheta
    (shiftAfter r t) word owner factors
    (fun v hv => native_successor_column_le oldTheta newTheta r t bound v
      (wordBound v hv) preserved increasing) ho hn certificate

end FullMarkedBLP
