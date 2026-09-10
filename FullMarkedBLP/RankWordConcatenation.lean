import FullMarkedBLP.RankCertificateReindex

namespace FullMarkedBLP

theorem naturalCutoff_cons_of_nonempty {alpha : Type u}
    (action : Nat → alpha → alpha) (theta : Nat → alpha) (v : Nat) {tail : List Nat}
    (nonempty : tail ≠ []) :
    naturalCutoff action theta (v :: tail) = (naturalCutoff action theta tail).map (action v) := by
  cases tail with
  | nil => contradiction
  | cons w rest => rfl

theorem naturalCutoff_append_of_nonempty {alpha : Type u}
    (action : Nat → alpha → alpha) (theta : Nat → alpha) (front : List Nat) {tail : List Nat}
    (nonempty : tail ≠ []) :
    naturalCutoff action theta (front ++ tail) =
      (naturalCutoff action theta tail).map (evalWord action front) := by
  induction front with
  | nil => simp [evalWord]
  | cons v front ih =>
    rw [List.cons_append, naturalCutoff_cons_of_nonempty action theta v (by simp [nonempty]), ih,
      Option.map_map]
    rfl

theorem rankWordEmbedding_append {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (front tail : List Nat) :
    rankWordEmbedding embedding (front ++ tail) =
      (rankWordEmbedding embedding front).comp (rankWordEmbedding embedding tail) := by
  apply FirstOrder.Language.ElementaryEmbedding.ext
  intro x
  change rankWordEmbedding embedding (front ++ tail) x =
    rankWordEmbedding embedding front (rankWordEmbedding embedding tail x)
  simp only [rankWordEmbedding_apply, evalWord_append]

theorem rankWordEmbedding_reindex {lambda : Ordinal.{u}}
    (oldEmbedding newEmbedding : Nat → RankElementaryEmbedding lambda)
    (phi : Nat → Nat) (word : List Nat)
    (factors : ∀ v ∈ word, newEmbedding (phi v) = oldEmbedding v) :
    rankWordEmbedding newEmbedding (word.map phi) = rankWordEmbedding oldEmbedding word := by
  apply FirstOrder.Language.ElementaryEmbedding.ext
  intro x
  simp only [rankWordEmbedding_apply]
  exact evalWord_reindex _ _ phi word
    (fun v hv => congrArg (fun k : RankElementaryEmbedding lambda => (k : RankDomain lambda → RankDomain lambda))
      (factors v hv)) x

end FullMarkedBLP
