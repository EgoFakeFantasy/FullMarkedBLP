import FullMarkedBLP.RankRowRealization

namespace FullMarkedBLP

/-- Saturated row semantics on one genuine rank domain. The complete
first-triple linedness family is added and preserved in FullRankRealization. -/
structure RankMarkedRealization {lambda : Ordinal.{u}} (a : Pattern)
    (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda) : Prop where
  valid : ∀ r row, rowAt a r = some row → row.CoreValid r
  proper : ∀ r row, rowAt a r = some row → row.ProperMarks r
  sat : Sat a
  increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j
  cardinals : ∀ i, i ≤ a.length + 1 → ∃ k : Cardinal.{u}, k.ord = (theta i).val
  edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (rankOrdinalAction (embedding r)) theta r
  critical : ∀ r row minimum, rowAt a r = some row → row.core.head? = some minimum →
    RankCriticalPoint (embedding r) (theta minimum)
  marked : ∀ r row y, rowAt a r = some row → y ∈ row.marks →
    ∃ k s xs delta, row.step ≤ k ∧ row.core[k]? = some y ∧ row.core[k - row.step]? = some s ∧
      Trace a s y xs ∧ naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (embedding r) (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast)

theorem rankMarkedRealization_toRows {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) : RankRowRealization a theta embedding :=
  ⟨h.valid, h.proper, h.increasing, h.cardinals, h.edges, h.critical, h.marked⟩

theorem rankRowRealization_with_sat {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) (hs : Sat a) : RankMarkedRealization a theta embedding :=
  ⟨h.valid, h.proper, hs, h.increasing, h.cardinals, h.edges, h.critical, h.marked⟩


theorem rankMarkedRealization_hasTraces {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) :
    ∀ r row, rowAt a r = some row → row.HasTraces a := by
  exact rankRowRealization_hasTraces (rankMarkedRealization_toRows h)

/-- Cut retains the same ambient rank domain, cardinal sequence and embeddings. -/
theorem rankMarkedRealization_cut {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) (hc : cut a = some b) :
    RankMarkedRealization b theta embedding := by
  exact rankRowRealization_with_sat
    (rankRowRealization_cut (rankMarkedRealization_toRows h) hc)
    (cut_preserves_sat h.valid h.sat hc)

end FullMarkedBLP
