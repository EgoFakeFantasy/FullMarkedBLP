import FullMarkedBLP.RankApplicationPowers
import FullMarkedBLP.RootRankRealization

namespace FullMarkedBLP

/-- The concrete coherent root sequence constructed by the second-order
reflection argument. Existence is not included in the definition of I2. -/
structure RankCoherentRoots {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) where
  embedding : Nat → RankElementaryEmbedding lambda
  critical : Nat → OrdinalDomain lambda
  criticalPoint : ∀ n, RankCriticalPoint (embedding n) (critical n)
  coherent : ∀ n, embedding n =
    rankApply hl (rankCriticalSequenceEmbedding hl (embedding (n + 1)) n) (embedding (n + 1))

namespace RankCoherentRoots

theorem power {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda} (r : RankCoherentRoots hl) (n : Nat) :
    rankCriticalSequenceEmbedding hl (r.embedding n) n = r.embedding 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rankCriticalSequenceEmbedding hl (r.embedding (n + 1)) (n + 1) =
          rankCriticalSequenceEmbedding hl
            (rankApply hl (rankCriticalSequenceEmbedding hl (r.embedding (n + 1)) n) (r.embedding (n + 1))) n :=
        (rankCriticalSequenceEmbedding_root_identity hl _ n).symm
      _ = rankCriticalSequenceEmbedding hl (r.embedding n) n := by rw [← r.coherent n]
      _ = r.embedding 0 := ih

theorem critical_step {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    (r : RankCoherentRoots hl) (n : Nat) :
    r.critical n = rankOrdinalAction (rankCriticalSequenceEmbedding hl (r.embedding (n + 1)) n)
      (r.critical (n + 1)) := by
  have cp := rankApply_criticalPoint hl (rankCriticalSequenceEmbedding hl (r.embedding (n + 1)) n)
    (r.criticalPoint (n + 1))
  rw [← r.coherent n] at cp
  exact rankCriticalPoint_unique (r.criticalPoint n) cp

/-- Passing to the previous root deletes exactly the indicated critical
image. This records both the retained prefix and the entire common tail. -/
theorem sequence_step {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    (r : RankCoherentRoots hl) (n m : Nat) :
    rankCriticalSequence (r.embedding n) (r.critical n) m =
      rankCriticalSequence (r.embedding (n + 1)) (r.critical (n + 1))
        (if m < n then m else m + 1) := by
  rw [r.critical_step n, r.coherent n, rankCriticalSequence_apply_image]
  exact rankCriticalSequenceEmbedding_on_sequence hl (r.criticalPoint (n + 1)) n m

theorem endpoint {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    (r : RankCoherentRoots hl) (n : Nat) :
    rankCriticalSequence (r.embedding n) (r.critical n) n = r.critical 0 := by
  have cp := rankCriticalSequenceEmbedding_criticalPoint hl (r.criticalPoint n) n
  rw [r.power n] at cp
  exact rankCriticalPoint_unique cp (r.criticalPoint 0)

theorem critical_succ {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    (r : RankCoherentRoots hl) (n : Nat) : r.critical (n + 1) = r.critical 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have same := r.sequence_step (n + 1) 0
    simp only [if_pos (by omega : 0 < n + 1), rankCriticalSequence] at same
    exact same.symm.trans ih

theorem first_succ_succ {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    (r : RankCoherentRoots hl) (n : Nat) :
    rankCriticalSequence (r.embedding (n + 2)) (r.critical (n + 2)) 1 =
      rankCriticalSequence (r.embedding 2) (r.critical 2) 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have same := r.sequence_step (n + 2) 1
    rw [if_pos (by omega : 1 < n + 2)] at same
    exact same.symm.trans ih

/-- The complete common-endpoint family, derived from coherence rather
than obtained by truncating one infinite critical sequence. -/
theorem endpoint_embeddings {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    (r : RankCoherentRoots hl) (k : Nat) (positive : 0 < k) :
    ∃ j : RankElementaryEmbedding lambda, RankCriticalPoint j (r.critical 1) ∧
      rankOrdinalAction j (r.critical 1) = rankCriticalSequence (r.embedding 2) (r.critical 2) 1 ∧
      rankCriticalSequence j (r.critical 1) (k + 1) = r.critical 0 := by
  refine ⟨r.embedding (k + 1), ?_, ?_, ?_⟩
  · simpa only [r.critical_succ k] using r.criticalPoint (k + 1)
  · rw [← r.critical_succ k]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    exact r.first_succ_succ n
  · simpa only [r.critical_succ k] using r.endpoint (k + 1)

theorem full_root {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    (r : RankCoherentRoots hl) :
    ∃ (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda),
      RankFullMarkedRealization start theta embedding ∧
        theta 0 = r.critical 1 ∧
        theta 1 = rankCriticalSequence (r.embedding 2) (r.critical 2) 1 ∧
        theta 2 = r.critical 0 :=
  rankFullMarkedRealization_root_of_endpoint_embeddings hl r.endpoint_embeddings

end RankCoherentRoots
end FullMarkedBLP
