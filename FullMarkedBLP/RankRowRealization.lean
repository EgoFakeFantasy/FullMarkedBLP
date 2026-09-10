import FullMarkedBLP.RankAgreementCritical

namespace FullMarkedBLP

/-- The row semantics before imposing Sat: valid ordered columns, genuine
edge and critical-point equations, and all natural-cutoff mark certificates.
The saturated structure extends these requirements in RankMarkedRealization. -/
structure RankRowRealization {lambda : Ordinal.{u}} (a : Pattern)
    (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda) : Prop where
  valid : ∀ r row, rowAt a r = some row → row.CoreValid r
  proper : ∀ r row, rowAt a r = some row → row.ProperMarks r
  increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j
  cardinals : ∀ i, i ≤ a.length + 1 → ∃ k : Cardinal.{u}, k.ord = (theta i).val
  edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (rankOrdinalAction (embedding r)) theta r
  critical : ∀ r row minimum, rowAt a r = some row → row.core.head? = some minimum →
    RankCriticalPoint (embedding r) (theta minimum)
  marked : ∀ r row y, rowAt a r = some row → y ∈ row.marks →
    ∃ k s xs delta, row.step ≤ k ∧ row.core[k]? = some y ∧ row.core[k - row.step]? = some s ∧
      Trace a s y xs ∧ naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (embedding r) (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast)

theorem rankRowRealization_hasTraces {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) :
    ∀ r row, rowAt a r = some row → row.HasTraces a := by
  intro r row hr y hy
  obtain ⟨k, s, xs, delta, hk, hky, hks, ht, _, _⟩ := h.marked r row y hr hy
  exact ⟨k, s, xs, hk, hky, hks, ht⟩

/-- Cut retains the same ambient rank domain, cardinal sequence and embeddings. -/
theorem rankRowRealization_cut {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) (hc : cut a = some b) :
    RankRowRealization b theta embedding := by
  have hpre := cut_is_prefix hc
  have hlen := hpre.length_le
  have hold : ∀ r row, rowAt b r = some row → rowAt a r = some row :=
    fun r row hr => (prefix_rowAt hpre (rowAt_bounds hr).2).trans hr
  refine ⟨cut_preserves_coreValid h.valid hc, cut_preserves_properMarks h.proper hc,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    exact h.increasing i j hij (by omega)
  · intro i hi
    exact h.cardinals i (by omega)
  · intro r row hr
    exact h.edges r row (hold r row hr)
  · intro r row minimum hr hm
    exact h.critical r row minimum (hold r row hr) hm
  · intro r row y hr hy
    have ha := hold r row hr
    obtain ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hw⟩ := h.marked r row y ha hy
    have hyr := (h.proper r row ha).2 y hy
    have hrb := (rowAt_bounds hr).2
    refine ⟨k, s, xs, delta, hk, hky, hks, ?_, hd, hw⟩
    exact trace_prefix h.valid ht (show y < b.length + 1 by omega)
      (fun i hi => prefix_rowAt hpre (by omega))

end FullMarkedBLP
