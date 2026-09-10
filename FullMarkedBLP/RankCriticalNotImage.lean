import FullMarkedBLP.RankCriticalPoint

namespace FullMarkedBLP

theorem rankCriticalPoint_not_ordinalImage {lambda : Ordinal.{u}}
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint j critical) (a : OrdinalDomain lambda) :
    rankOrdinalAction j a ≠ critical := by
  intro equal
  by_cases below : a < critical
  · have fixed := cp.2 a below
    have same : a = critical := fixed.symm.trans equal
    exact (ne_of_lt below) same
  · have upper := rankOrdinalAction_monotone j (le_of_not_gt below)
    rw [equal] at upper
    exact (not_le_of_gt (rankCriticalPoint_lt_image cp)) upper

/-- The critical ordinal cannot be the image of any set in the rank domain. -/
theorem rankCriticalPoint_not_image {lambda : Ordinal.{u}}
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint j critical) (x : RankDomain lambda) :
    j x ≠ ordinalDomainElement critical := by
  intro equal
  have ordinal : ZFSet.IsOrdinal x.val := (rankElementary_isOrdinal_iff j x).mp (by
    rw [equal]
    exact ZFSet.isOrdinal_toZFSet critical.val)
  let a : OrdinalDomain lambda := ⟨x.val.rank, x.property⟩
  have same : ordinalDomainElement a = x := Subtype.ext ordinal.toZFSet_rank_eq
  apply rankCriticalPoint_not_ordinalImage cp a
  apply Subtype.ext
  change (j (ordinalDomainElement a)).val.rank = critical.val
  rw [same, equal]
  exact Ordinal.rank_toZFSet _

end FullMarkedBLP
