import FullMarkedBLP.CopySemanticValues
import FullMarkedBLP.CopyPredecessor

namespace FullMarkedBLP

/-- The literal full-row map also maps the implicit endpoint to the new
implicit endpoint. This is needed for every edge, including terminal edges. -/
theorem copiedCore_maps_full {n source p : Nat} {last row : Row} {core : List Nat}
    (valid : last.CoreValid n) (hp : last.p = some p) (hsp : p ≤ source)
    (copied : copiedCore n last source row = some core) :
    MapsEntries (copyEntry n last) (row.full source) (core ++ [source + (n - p) + 1]) := by
  obtain ⟨full, mapped, result⟩ := Option.bind_eq_some_iff.mp copied
  cases Option.some.inj result
  have maps := option_mapM_forall2 mapped
  obtain ⟨endpoint, endpointAt, endpointMap⟩ := maps.last
    (by simp [Row.full] : (row.full source).getLast? = some (source + 1))
  have endpointValue := copyEntry_high_value valid hp (by omega : p ≤ source + 1) endpointMap
  obtain ⟨front, shape⟩ := List.getLast?_eq_some_iff.mp endpointAt
  have same : full.dropLast ++ [source + (n - p) + 1] = full := by
    rw [shape]
    simp only [List.dropLast_concat]
    congr 2
    omega
  rw [same]
  exact maps

/-- Actual copied rows realize all step edges under the applied owner,
including the edge whose target is the implicit endpoint. -/
theorem copiedRow_realizesEdges {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last row copied : Row} {source p : Nat}
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p)
    (sourceAt : rowAt a source = some row) (hsp : p ≤ source)
    (copy : copiedRow a last source row = some copied) :
    copied.RealizesEdges (rankOrdinalAction (rankApply hl (embedding a.length) (embedding source)))
      (shortCopyColumnValues theta (embedding a.length) a.length p) (source + (a.length - p)) := by
  obtain ⟨core, copiedCoreEq, result⟩ := Option.bind_eq_some_iff.mp copy
  cases Option.some.inj result
  have maps := copiedCore_maps_full (h.valid a.length last lastAt) hp hsp copiedCoreEq
  intro i x y sourceValue targetValue
  obtain ⟨oldX, oldSource, sourceMap⟩ := maps.at sourceValue
  obtain ⟨oldY, oldTarget, targetMap⟩ := maps.at targetValue
  rw [copyEntry_semantic_image h lastAt hp sourceMap,
    copyEntry_semantic_image h lastAt hp targetMap, rankApply_ordinal_image]
  rw [h.edges source row sourceAt i oldX oldY oldSource oldTarget]

/-- The copied minimum is exactly the transported critical point. -/
theorem copiedRow_criticalPoint {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last row copied : Row} {source p minimum : Nat}
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p)
    (sourceAt : rowAt a source = some row)
    (copy : copiedRow a last source row = some copied) (headAt : copied.core.head? = some minimum) :
    RankCriticalPoint (rankApply hl (embedding a.length) (embedding source))
      (shortCopyColumnValues theta (embedding a.length) a.length p minimum) := by
  obtain ⟨core, copiedCoreEq, result⟩ := Option.bind_eq_some_iff.mp copy
  cases Option.some.inj result
  have minimumAt : core[0]? = some minimum := by simpa only [List.head?_eq_getElem?] using headAt
  obtain ⟨oldMinimum, oldMinimumAt, minimumMap⟩ := (copiedCore_maps_entries copiedCoreEq).at minimumAt
  have oldHead : row.core.head? = some oldMinimum := by simpa only [List.head?_eq_getElem?] using oldMinimumAt
  rw [copyEntry_semantic_image h lastAt hp minimumMap]
  exact rankApply_criticalPoint hl (embedding a.length) (h.critical source row oldMinimum sourceAt oldHead)

end FullMarkedBLP
