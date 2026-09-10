import FullMarkedBLP.RankCriticalSequenceInaccessible

namespace FullMarkedBLP

/-- The supremum is an external ordinal; it is not assumed to belong to
the embedding's rank domain. Kunen cofinality will identify it with lambda. -/
noncomputable def rankCriticalSupremum {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (critical : OrdinalDomain lambda) : Ordinal.{u} :=
  ⨆ n, (rankCriticalSequence j critical n).val

theorem rankCriticalSequence_lt_supremum {lambda : Ordinal.{u}}
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint j critical) (n : Nat) :
    (rankCriticalSequence j critical n).val < rankCriticalSupremum j critical := by
  have less : (rankCriticalSequence j critical n).val < (rankCriticalSequence j critical (n + 1)).val :=
    (rankCriticalSequence_strictMono cp) (Nat.lt_succ_self n)
  exact less.trans_le
    (Ordinal.le_iSup (fun i => (rankCriticalSequence j critical i).val) (n + 1))

theorem rankCriticalSupremum_le_domain {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (critical : OrdinalDomain lambda) :
    rankCriticalSupremum j critical ≤ lambda :=
  Ordinal.iSup_le fun n => (rankCriticalSequence j critical n).property.le

theorem rankCriticalSupremum_cofinal {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (critical : OrdinalDomain lambda)
    {b : Ordinal.{u}} (below : b < rankCriticalSupremum j critical) :
    ∃ n, b < (rankCriticalSequence j critical n).val := Ordinal.lt_iSup_iff.mp below

theorem rankCriticalSupremum_cardinal {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    (rankCriticalSupremum j critical).card.ord = rankCriticalSupremum j critical := by
  apply le_antisymm (Cardinal.ord_card_le _)
  apply Ordinal.iSup_le
  intro n
  obtain ⟨c, hc⟩ := rankCriticalSequence_cardinal hl cp n
  have eq : (rankCriticalSequence j critical n).val.card.ord = (rankCriticalSequence j critical n).val := by
    rw [← hc, Cardinal.card_ord]
  rw [← eq]
  exact Cardinal.ord_le_ord.mpr
    (Ordinal.card_le_card (Ordinal.le_iSup (fun i => (rankCriticalSequence j critical i).val) n))

theorem rankCriticalSupremum_cof {lambda : Ordinal.{u}}
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint j critical) :
    (rankCriticalSupremum j critical).cof = Cardinal.aleph0 := by
  have increasing : StrictMono (fun n => (rankCriticalSequence j critical n).val) :=
    rankCriticalSequence_strictMono cp
  simpa [rankCriticalSupremum, Order.cof_nat] using Ordinal.lift_cof_iSup increasing

theorem rankCriticalSupremum_isSuccLimit {lambda : Ordinal.{u}}
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint j critical) :
    Order.IsSuccLimit (rankCriticalSupremum j critical) := by
  apply Ordinal.one_lt_cof_iff.mp
  rw [rankCriticalSupremum_cof cp]
  exact Cardinal.one_lt_aleph0

theorem rankCriticalSupremum_isStrongLimit {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    Cardinal.IsStrongLimit (rankCriticalSupremum j critical).card := by
  refine ⟨?_, ?_⟩
  · intro zero
    have nonzero := (rankCriticalSupremum_isSuccLimit cp).ne_zero
    apply nonzero
    rw [← rankCriticalSupremum_cardinal hl cp, zero, Cardinal.ord_zero]
  · intro d below
    have ordinalBelow : d.ord < rankCriticalSupremum j critical := by
      rw [← rankCriticalSupremum_cardinal hl cp]
      exact Cardinal.ord_lt_ord.mpr below
    obtain ⟨n, hn⟩ := rankCriticalSupremum_cofinal j critical ordinalBelow
    obtain ⟨c, hc⟩ := rankCriticalSequence_cardinal hl cp n
    have cardEq : (rankCriticalSequence j critical n).val.card = c := by rw [← hc, Cardinal.card_ord]
    have smaller : d < (rankCriticalSequence j critical n).val.card := by
      rw [cardEq, ← Cardinal.ord_lt_ord, hc]
      exact hn
    have strong := rankCriticalPoint_isStrongLimit hl (rankCriticalSequenceEmbedding_criticalPoint hl cp n)
    exact (strong.isStrongPrelimit smaller).trans_le
      (Ordinal.card_le_card (Ordinal.le_iSup (fun i => (rankCriticalSequence j critical i).val) n))

end FullMarkedBLP
