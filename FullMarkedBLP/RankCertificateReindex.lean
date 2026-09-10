import FullMarkedBLP.CutoffReindex

namespace FullMarkedBLP

theorem evalWord_reindex {alpha : Type u} (oldAction newAction : Nat → alpha → alpha)
    (phi : Nat → Nat) (word : List Nat)
    (factors : ∀ v ∈ word, newAction (phi v) = oldAction v) (x : alpha) :
    evalWord newAction (word.map phi) x = evalWord oldAction word x := by
  induction word with
  | nil => rfl
  | cons v tail ih =>
    simp only [List.map_cons, evalWord]
    rw [factors v (by simp), ih (fun i hi => factors i (List.mem_cons_of_mem v hi))]

/-- Historical weak certificates survive reindexing preserved factors and
lowering the successor columns used by their natural cutoff. This does not
assert that a particular syntactic operation meets these hypotheses. -/
theorem rankCertificate_reindex {lambda : Ordinal.{u}}
    (oldEmbedding newEmbedding : Nat → RankElementaryEmbedding lambda)
    (oldTheta newTheta : Nat → OrdinalDomain lambda) (phi : Nat → Nat) (word : List Nat)
    (owner : RankElementaryEmbedding lambda)
    (factors : ∀ v ∈ word, newEmbedding (phi v) = oldEmbedding v)
    (successors : ∀ v ∈ word, newTheta (phi v + 1) ≤ oldTheta (v + 1))
    {oldDelta newDelta : OrdinalDomain lambda}
    (ho : naturalCutoff (fun i => rankOrdinalAction (oldEmbedding i)) oldTheta word = some oldDelta)
    (hn : naturalCutoff (fun i => rankOrdinalAction (newEmbedding i)) newTheta (word.map phi) = some newDelta)
    (certificate : rankCutoffAgreement oldDelta.val owner
      (evalWord (fun i => (oldEmbedding i : RankDomain lambda → RankDomain lambda)) word)) :
    rankCutoffAgreement newDelta.val owner
      (evalWord (fun i => (newEmbedding i : RankDomain lambda → RankDomain lambda)) (word.map phi)) := by
  have hd : newDelta ≤ oldDelta := naturalCutoff_reindex_le
    (fun i => rankOrdinalAction (oldEmbedding i)) (fun i => rankOrdinalAction (newEmbedding i))
    oldTheta newTheta phi word (fun i => rankOrdinalAction_monotone (oldEmbedding i))
    (fun v hv => congrArg rankOrdinalAction (factors v hv)) successors ho hn
  intro x z hx hz
  have he := evalWord_reindex
    (fun i => (oldEmbedding i : RankDomain lambda → RankDomain lambda))
    (fun i => (newEmbedding i : RankDomain lambda → RankDomain lambda)) phi word
    (fun v hv => by dsimp only; rw [factors v hv]) z
  rw [he]
  exact certificate x z (lt_of_lt_of_le hx hd) (lt_of_lt_of_le hz hd)

end FullMarkedBLP

