import FullMarkedBLP.RankClassImageComposition
import FullMarkedBLP.RankCriticalSequenceInaccessible

namespace FullMarkedBLP

theorem rankCriticalSequenceEmbedding_apply {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (n : Nat) :
    rankCriticalSequenceEmbedding hl (rankApply hl j k) n =
      rankApply hl j (rankCriticalSequenceEmbedding hl k n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rankCriticalSequenceEmbedding, ih]
    exact (rankApply_left_distrib hl j k (rankCriticalSequenceEmbedding hl k n)).symm

theorem rankCriticalSequenceEmbedding_square {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (n : Nat) :
    rankApply hl (rankCriticalSequenceEmbedding hl j n) (rankCriticalSequenceEmbedding hl j n) =
      rankCriticalSequenceEmbedding hl j (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rankApply hl (rankApply hl j (rankCriticalSequenceEmbedding hl j n))
      (rankApply hl j (rankCriticalSequenceEmbedding hl j n)) = _
    rw [← rankApply_left_distrib hl, ih]
    rfl

/-- The algebraic identity used to keep the successive roots coherent. -/
theorem rankCriticalSequenceEmbedding_root_identity {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (n : Nat) :
    rankCriticalSequenceEmbedding hl (rankApply hl (rankCriticalSequenceEmbedding hl j n) j) n =
      rankCriticalSequenceEmbedding hl j (n + 1) := by
  rw [rankCriticalSequenceEmbedding_apply, rankCriticalSequenceEmbedding_square]

theorem rankCriticalSequence_apply_image {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (critical : OrdinalDomain lambda) (n : Nat) :
    rankCriticalSequence (rankApply hl j k) (rankOrdinalAction j critical) n =
      rankOrdinalAction j (rankCriticalSequence k critical n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rankCriticalSequence, ih]
    exact rankApply_ordinal_image hl j k _

theorem rankCriticalSequenceEmbedding_on_tail {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (critical : OrdinalDomain lambda) (n m : Nat) :
    rankOrdinalAction (rankCriticalSequenceEmbedding hl j n) (rankCriticalSequence j critical (n + m)) =
      rankCriticalSequence j critical (n + m + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have image := rankApply_ordinal_image hl j (rankCriticalSequenceEmbedding hl j n)
      (rankCriticalSequence j critical (n + m))
    rw [ih] at image
    convert image using 1 <;> simp only [rankCriticalSequenceEmbedding, Nat.succ_add, rankCriticalSequence]

theorem rankCriticalSequenceEmbedding_fixes_prefix {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    {n m : Nat} (before : m < n) :
    rankOrdinalAction (rankCriticalSequenceEmbedding hl j n) (rankCriticalSequence j critical m) =
      rankCriticalSequence j critical m :=
  (rankCriticalSequenceEmbedding_criticalPoint hl cp n).2 _ (rankCriticalSequence_strictMono cp before)

theorem rankCriticalSequenceEmbedding_on_sequence {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (n m : Nat) :
    rankOrdinalAction (rankCriticalSequenceEmbedding hl j n) (rankCriticalSequence j critical m) =
      rankCriticalSequence j critical (if m < n then m else m + 1) := by
  by_cases before : m < n
  · rw [if_pos before]
    exact rankCriticalSequenceEmbedding_fixes_prefix hl cp before
  · rw [if_neg before]
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    exact rankCriticalSequenceEmbedding_on_tail hl j critical n r

end FullMarkedBLP
