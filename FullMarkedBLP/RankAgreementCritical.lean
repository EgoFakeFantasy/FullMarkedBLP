import FullMarkedBLP.RankCriticalPoint

namespace FullMarkedBLP

theorem rankAgreement_moves_ordinal {lambda delta : Ordinal.{u}}
    {j k : RankElementaryEmbedding lambda} (h : rankCutoffAgreement delta j k)
    {o : OrdinalDomain lambda} (ho : o.val < delta)
    (hm : rankOrdinalAction j o ≠ o) : rankOrdinalAction k o ≠ o := by
  have hv : (ordinalDomainElement o).val.rank < delta := by
    simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using ho
  have hmem : (ordinalDomainElement o).val ∈ (j (ordinalDomainElement o)).val := by
    rw [rankOrdinalAction_compat]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (rankOrdinalAction_moved_up j hm)
  have hk := (h (ordinalDomainElement o) (ordinalDomainElement o) hv hv).mp hmem
  rw [rankOrdinalAction_compat] at hk
  have hlt : o < rankOrdinalAction k o := Ordinal.toZFSet_mem_toZFSet_iff.mp hk
  exact ne_of_gt hlt

/-- One visible critical point forces the other below the same cutoff, so no
    separate visibility assumption for the second critical point is needed. -/
theorem rankAgreement_critical_eq {lambda delta : Ordinal.{u}}
    {j k : RankElementaryEmbedding lambda} {c d : OrdinalDomain lambda}
    (h : rankCutoffAgreement delta j k) (hc : RankCriticalPoint j c)
    (hd : RankCriticalPoint k d) (hvisible : c.val < delta) : c = d := by
  have hdc : d ≤ c := rankCriticalPoint_le_moved hd (rankAgreement_moves_ordinal h hvisible hc.1)
  have hdvisible : d.val < delta := lt_of_le_of_lt hdc hvisible
  have hsym : rankCutoffAgreement delta k j := fun x z hx hz => (h x z hx hz).symm
  have hcd : c ≤ d := rankCriticalPoint_le_moved hc (rankAgreement_moves_ordinal hsym hdvisible hd.1)
  exact le_antisymm hcd hdc

/-- A visible critical point also proves that the weakly agreeing elementary
    embedding has a critical point, without a separate moved-ordinal witness. -/
theorem rankAgreement_transfers_critical {lambda delta : Ordinal.{u}}
    {j k : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda}
    (h : rankCutoffAgreement delta j k) (hc : RankCriticalPoint j c)
    (hvisible : c.val < delta) : RankCriticalPoint k c := by
  obtain ⟨d, hd⟩ := rankCriticalPoint_exists k ⟨c, rankAgreement_moves_ordinal h hvisible hc.1⟩
  have he := rankAgreement_critical_eq h hc hd hvisible
  simpa only [he] using hd

end FullMarkedBLP
