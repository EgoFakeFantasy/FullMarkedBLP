import FullMarkedBLP.RankCriticalSequence
import FullMarkedBLP.RankLinedWitness

namespace FullMarkedBLP

theorem rankCriticalSequence_selfApply {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (critical : OrdinalDomain lambda) (n : Nat) :
    rankOrdinalAction (rankApply hl j j) (rankCriticalSequence j critical (n + 1)) =
      rankCriticalSequence j critical (n + 2) := by
  exact rankApply_ordinal_image hl j j (rankCriticalSequence j critical n)

/-- Starting at j, repeatedly apply j(j) to obtain one factor for each
successive interval of j's critical sequence, all with the same critical point. -/
noncomputable def rankLiningFactor {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) : Nat → RankElementaryEmbedding lambda
  | 0 => j
  | n + 1 => rankApply hl (rankApply hl j j) (rankLiningFactor hl j n)

theorem rankLiningFactor_spec {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint j critical) (n : Nat) :
    RankCriticalPoint (rankLiningFactor hl j n) critical ∧
    rankOrdinalAction (rankLiningFactor hl j n) critical = rankCriticalSequence j critical (n + 1) ∧
    rankOrdinalAction (rankLiningFactor hl j n) (rankCriticalSequence j critical (n + 1)) =
      rankCriticalSequence j critical (n + 2) := by
  have fixed : rankOrdinalAction (rankApply hl j j) critical = critical :=
    (rankApply_criticalPoint hl j cp).2 critical (rankCriticalPoint_lt_image cp)
  induction n with
  | zero => exact ⟨cp, rfl, rfl⟩
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · have moved := rankApply_criticalPoint hl (rankApply hl j j) ih.1
      rwa [fixed] at moved
    · have first := rankApply_ordinal_image hl (rankApply hl j j) (rankLiningFactor hl j n) critical
      rw [fixed, ih.2.1, rankCriticalSequence_selfApply] at first
      exact first
    · have second := rankApply_ordinal_image hl (rankApply hl j j) (rankLiningFactor hl j n)
        (rankCriticalSequence j critical (n + 1))
      rw [rankCriticalSequence_selfApply, ih.2.2] at second
      have next : rankOrdinalAction (rankApply hl j j) (rankCriticalSequence j critical (n + 2)) =
          rankCriticalSequence j critical (n + 3) := rankCriticalSequence_selfApply hl j critical (n + 1)
      rw [next] at second
      exact second

/-- A complete k-step witness from the first critical image through the
(k+1)-st critical image, with its final endpoint recorded explicitly. -/
noncomputable def rankCriticalSequence_linedWitness {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (k : Nat) (positive : 0 < k) :
    RankLinedWitness k critical (rankCriticalSequence j critical 1) (rankCriticalSequence j critical (k + 1)) where
  point i := rankCriticalSequence j critical (i + 1)
  factor i := rankLiningFactor hl j i
  positive := positive
  critical_lt := rankCriticalPoint_lt_image cp
  start := rfl
  finish := rfl
  increasing i j hij _ := rankCriticalSequence_strictMono cp (by omega : i + 1 < j + 1)
  criticalPoint i _ := (rankLiningFactor_spec hl cp i).1
  firstEdge i _ := (rankLiningFactor_spec hl cp i).2.1
  secondEdge i _ := (rankLiningFactor_spec hl cp i).2.2

/-- A family of elementary embeddings whose finite critical sequences land
at one common endpoint supplies the manuscript's whole witness family.
Producing these embeddings from I2 remains a separate existence theorem. -/
theorem rankAllFiniteLined_of_endpoint_embeddings {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {critical left right : OrdinalDomain lambda}
    (family : ∀ k, 0 < k → ∃ j : RankElementaryEmbedding lambda,
      RankCriticalPoint j critical ∧ rankOrdinalAction j critical = left ∧
        rankCriticalSequence j critical (k + 1) = right) :
    RankAllFiniteLined critical left right := by
  intro k positive
  obtain ⟨j, cp, first, last⟩ := family k positive
  have witness := rankCriticalSequence_linedWitness hl cp k positive
  have start : rankCriticalSequence j critical 1 = left := first
  rw [start, last] at witness
  exact ⟨witness⟩

end FullMarkedBLP
