import FullMarkedBLP.CopySemanticRows
import FullMarkedBLP.CopySemanticColumns
import FullMarkedBLP.RankTraceGeometry

namespace FullMarkedBLP

/-- The literal one-based copy guard bounds the next source column, whose
step edge covers the successor of the marked target. -/
theorem realized_copyGuard_successor_bound {lambda : Ordinal.{u}}
    {row : Row} {owner minimum k x : Nat} {theta : Nat → OrdinalDomain lambda}
    {j : RankElementaryEmbedding lambda} (valid : row.CoreValid owner)
    (increasing : ∀ i v, i < v → v ≤ owner + 1 → theta i < theta v)
    (edges : row.RealizesEdges (rankOrdinalAction j) theta owner)
    (minimumBound : minimum ≤ owner) (stepBound : row.step ≤ k)
    (markAt : row.core[k]? = some x) (markBound : x < owner)
    (guard : copyPositionGuard row.core row.step k minimum = true) :
    theta (x + 1) ≤ rankOrdinalAction j (theta minimum) := by
  have lastAt : row.core[row.core.length - 1]? = some owner := by
    simpa only [List.getLast?_eq_getElem?] using valid.2.2.1
  have indexBound := sorted_index_lt_of_value_lt valid.1 markAt lastAt markBound
  have targetIndex : k + 1 < row.core.length := by omega
  let target := row.core[k + 1]'targetIndex
  have targetAt : row.core[k + 1]? = some target := List.getElem?_eq_getElem targetIndex
  have targetBound := core_entry_le_owner valid (List.mem_of_getElem? targetAt)
  have sourceIndex : k < row.core.length := (List.getElem?_eq_some_iff.mp markAt).1
  have targetLt : x < target := by
    have lt := List.pairwise_iff_getElem.mp valid.1 k (k + 1) sourceIndex targetIndex (by omega)
    have same := (List.getElem?_eq_some_iff.mp markAt).2
    simpa only [same] using lt
  have stepBound' : row.step ≤ k + 1 := by omega
  simp only [copyPositionGuard, if_pos stepBound'] at guard
  cases nextAt : row.core[k + 1 - row.step]? with
  | none => simp [nextAt] at guard
  | some next =>
    have nextBound : next ≤ minimum := by simpa only [nextAt, Option.any_some, decide_eq_true_eq] using guard
    have nextEdge : rankOrdinalAction j (theta next) = theta target := by
      apply edges (k + 1 - row.step) next target (full_entry_of_core nextAt)
      simpa only [show k + 1 - row.step + row.step = k + 1 by omega] using full_entry_of_core targetAt
    have lower : theta (x + 1) ≤ theta target := by
      by_cases same : x + 1 = target
      · exact (congrArg theta same).le
      · exact (increasing (x + 1) target (by omega) (by omega)).le
    have upper : theta next ≤ theta minimum := by
      by_cases same : next = minimum
      · exact (congrArg theta same).le
      · exact (increasing next minimum (by omega) (by omega)).le
    exact lower.trans (nextEdge.symm.le.trans (rankOrdinalAction_monotone j upper))

/-- The actual copied trace's natural cutoff is below the copied owner's
image of the removed last row's critical point. No copied mark certificate
is assumed to obtain this bound. -/
theorem shortCopy_guard_cutoff_bound {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last row : Row} {p e minimum r k s x : Nat} {word : List Nat} {delta : OrdinalDomain lambda}
    (copy : shortCopy a = some b) (lastAt : rowAt a a.length = some last)
    (hp : last.p = some p) (he : last.e = some e) (minimumAt : last.core.head? = some minimum)
    (rowAtCopy : rowAt b r = some row) (afterPrefix : a.length ≤ r)
    (stepBound : row.step ≤ k) (markAt : row.core[k]? = some x) (markBound : x < r)
    (guard : copyPositionGuard row.core row.step k minimum = true)
    (trace : Trace b s x word)
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
      (shortCopyColumnValues theta (embedding a.length) a.length p) word.dropLast = some delta) :
    delta ≤ rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p r) (theta minimum) := by
  have valid := shortCopy_preserves_coreValid h.valid copy
  have increasing := shortCopyColumnValues_increasing h copy lastAt hp he
  have edges := shortCopy_realizes_all_edges hl h copy lastAt hp he
  have cutoffBound := (rankTrace_cutoff_bounds valid increasing edges trace cutoff).2
  have minimumEntry : last.core[0]? = some minimum := by simpa only [List.head?_eq_getElem?] using minimumAt
  have minimumBound := core_entry_le_owner (h.valid a.length last lastAt) (List.mem_of_getElem? minimumEntry)
  have ownerBound := (rowAt_bounds rowAtCopy).2
  have guardBound := realized_copyGuard_successor_bound (valid r row rowAtCopy)
    (fun i v hiv hv => increasing i v hiv (by omega)) (edges r row rowAtCopy)
    (by omega : minimum ≤ r) stepBound markAt markBound guard
  rw [shortCopyColumnValues_prefix h lastAt hp minimumBound] at guardBound
  exact cutoffBound.trans guardBound

end FullMarkedBLP
