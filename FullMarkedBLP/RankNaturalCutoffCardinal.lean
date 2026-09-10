import FullMarkedBLP.RankCardinalPreservation
import FullMarkedBLP.RankCriticalLimit

namespace FullMarkedBLP

theorem rankNaturalCutoff_cardinal {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (embedding : Nat → RankElementaryEmbedding lambda) (theta : Nat → OrdinalDomain lambda)
    (word : List Nat) (columns : ∀ v ∈ word, ∃ c : Cardinal.{u}, c.ord = (theta (v + 1)).val)
    {delta : OrdinalDomain lambda}
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta word = some delta) :
    ∃ c : Cardinal.{u}, c.ord = delta.val := by
  induction word generalizing delta with
  | nil => simp [naturalCutoff] at cutoff
  | cons v tail ih =>
    cases tail with
    | nil =>
      have same : theta (v + 1) = delta := Option.some.inj cutoff
      rw [← same]
      exact columns v (by simp)
    | cons w rest =>
      obtain ⟨epsilon, tailCutoff⟩ := naturalCutoff_defined
        (fun i => rankOrdinalAction (embedding i)) theta (word := w :: rest) (by simp)
      have same : rankOrdinalAction (embedding v) epsilon = delta := by
        simpa only [naturalCutoff, tailCutoff, Option.map_some, Option.some.injEq] using cutoff
      rw [← same]
      exact (rankOrdinalAction_cardinal_iff hl (embedding v) epsilon).mpr
        (ih (fun i hi => columns i (List.mem_cons_of_mem v hi)) tailCutoff)

theorem rankRealization_trace_cutoff_cardinal {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {s y : Nat} {xs : List Nat} {delta : OrdinalDomain lambda} (trace : Trace a s y xs)
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta) :
    ∃ c : Cardinal.{u}, c.ord = delta.val := by
  apply rankNaturalCutoff_cardinal hl embedding theta xs.dropLast _ cutoff
  intro v hv
  obtain ⟨row, rowAtV⟩ := trace_factor_has_row trace hv
  have bound := (rowAt_bounds rowAtV).2
  exact h.cardinals (v + 1) (by omega)

theorem rankCardinal_isSuccLimit_above_critical {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c delta : OrdinalDomain lambda}
    (critical : RankCriticalPoint j c) (below : c ≤ delta)
    (cardinal : ∃ k : Cardinal.{u}, k.ord = delta.val) : Order.IsSuccLimit delta.val := by
  obtain ⟨k, value⟩ := cardinal
  have bound : Ordinal.omega0 ≤ delta.val :=
    (Ordinal.omega0_le_of_isSuccLimit (rankCriticalPoint_isSuccLimit hl critical)).trans below
  have infinite : Cardinal.aleph0 ≤ k := Cardinal.ord_le_ord.mp (by
    rw [Cardinal.ord_aleph0, value]
    exact bound)
  simpa only [value] using Cardinal.isSuccLimit_ord infinite

end FullMarkedBLP
