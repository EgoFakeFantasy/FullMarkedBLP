import FullMarkedBLP.RankAgreementEdges

namespace FullMarkedBLP

/-- For elementary ordinal actions, visibility of the known target already
implies visibility of its source. -/
theorem rankAgreement_reads_visible_target {lambda delta : Ordinal.{u}}
    {j k : RankElementaryEmbedding lambda} (h : rankCutoffAgreement delta j k)
    (hd : delta ≤ lambda) {source target : OrdinalDomain lambda}
    (ht : target.val < delta) (hj : rankOrdinalAction j source = target) :
    rankOrdinalAction k source = target := by
  have hst : source ≤ target := by
    simpa only [hj] using rankOrdinalAction_le_self_image j source
  exact rankAgreement_reads_ordinal_edge h hd (lt_of_le_of_lt hst ht) ht hj

/-- A single historical cutoff covering all packet targets transfers the whole
packet. The packet's edges and target coverage must be established separately. -/
theorem rankAgreement_reads_packet {lambda delta : Ordinal.{u}}
    {j k : RankElementaryEmbedding lambda} (h : rankCutoffAgreement delta j k)
    (hd : delta ≤ lambda) (packet : List (OrdinalDomain lambda × OrdinalDomain lambda))
    (known : ∀ pair ∈ packet, rankOrdinalAction j pair.1 = pair.2)
    (covered : ∀ pair ∈ packet, pair.2.val < delta) :
    ∀ pair ∈ packet, rankOrdinalAction k pair.1 = pair.2 := by
  intro pair hp
  exact rankAgreement_reads_visible_target h hd (covered pair hp) (known pair hp)

end FullMarkedBLP
