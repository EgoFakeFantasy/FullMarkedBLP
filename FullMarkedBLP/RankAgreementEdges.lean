import FullMarkedBLP.RealizedInterval

namespace FullMarkedBLP

/-- Weak rank agreement transfers an ordinal edge whose input and known output
are below the cutoff. No bound on the unknown output is required. -/
theorem rankAgreement_reads_ordinal_edge {lambda delta : Ordinal.{u}}
    {j k : RankElementaryEmbedding lambda} (h : rankCutoffAgreement delta j k)
    (hd : delta ≤ lambda) {source target : OrdinalDomain lambda}
    (hs : source.val < delta) (ht : target.val < delta)
    (hj : rankOrdinalAction j source = target) :
    rankOrdinalAction k source = target := by
  have hext := (rankCutoffAgreement_iff_extension hd).mp h
  have hin : (ordinalDomainElement source).val.rank < delta := by
    simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using hs
  have hknown : extendRankMap j (ordinalDomainElement source).val = target.val.toZFSet := by
    rw [extendRankMap_inside, rankOrdinalAction_compat, hj]
  have hord : ZFSet.IsOrdinal (extendRankMap k (ordinalDomainElement source).val) := by
    rw [extendRankMap_inside, rankOrdinalAction_compat]
    exact ZFSet.isOrdinal_toZFSet _
  have hout := zfcCutoffAgreement_reads_edge hext hin hknown hord ht
  rw [extendRankMap_inside, rankOrdinalAction_compat] at hout
  apply Subtype.ext
  have hrank := congrArg ZFSet.rank hout
  simpa only [Ordinal.rank_toZFSet] using hrank

end FullMarkedBLP

