import FullMarkedBLP.CompletionSemanticIntervals
import FullMarkedBLP.CompletionMinimum

namespace FullMarkedBLP

/-- Proper marks and the original critical point survive under the same local
packet geometry used for all-edge realization, without historyValid. -/
theorem rankRealization_completion_marks_critical {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r k y p nextTarget minimum : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (hm : y ∈ row.marks) (hmin : row.core.head? = some minimum)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (hs : sources.Nodup) (bounds : ∀ x ∈ sources, x ≤ a.length + 1)
    (gap : y + sources.length < nextTarget) (beforeOwner : y + sources.length < r)
    (packet : ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length)) :
    (completeMarkRow row y sources).ProperMarks r ∧
      (completeMarkRow row y sources).core.head? = some minimum ∧
      RankCriticalPoint (embedding r) (theta minimum) := by
  obtain ⟨left, right, hl, hrr, sourceGap, hdis, targetGap, below, hpy⟩ :=
    rankRealization_completion_geometry h hr hp hk hy hnt bounds gap beforeOwner packet
  have hv := h.valid r row hr
  have proper := h.proper r row hr
  refine ⟨completeMarkRow_properMarks hv proper hm hs hdis ?_ beforeOwner, ?_, h.critical r row minimum hr hmin⟩
  · intro x hx z hz
    obtain ⟨_, i, hi, hiz⟩ := proper.2 z hz
    exact lt_of_lt_of_le (below x hx) (target_position_after_p hv hi hiz hp)
  · apply completeMarkRow_preserves_minimum hv hmin (core_head_le_entry hv hmin hy)
    intro x hx
    exact (core_head_le_entry hv hmin hl).trans (sourceGap x hx).1.le

/-- Old marked certificates retain their exact words and natural cutoffs;
interval cases are derived from packet edges, not separately assumed. -/
theorem rankRealization_completion_old_certificates {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r k y p nextTarget : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (hs : sources.Nodup) (bounds : ∀ x ∈ sources, x ≤ a.length + 1)
    (gap : y + sources.length < nextTarget) (beforeOwner : y + sources.length < r)
    (packet : ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length)) :
    ∀ z ∈ row.marks, ∃ xs delta,
      MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r z xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  obtain ⟨left, right, hl, hrr, sourceGap, hdis, targetGap, below, hpy⟩ :=
    rankRealization_completion_geometry h hr hp hk hy hnt bounds gap beforeOwner packet
  intro z hz
  apply completion_old_rank_certificate h hr hz hs hdis targetGap
  intro i x hi hiz hix
  exact rankRealization_completion_old_intervals h hr hp hpy hi hiz hix bounds beforeOwner targetGap packet

/-- The semantic packet geometry also identifies every inserted marked source
position; the supplied parallel trace becomes the actual new MarkTrace. -/
theorem rankRealization_completion_new_markTrace {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r k y p nextTarget x : Nat} {row : Row}
    {sources xs : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (hs : sources.Nodup) (bounds : ∀ x ∈ sources, x ≤ a.length + 1)
    (gap : y + sources.length < nextTarget) (beforeOwner : y + sources.length < r)
    (packet : ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length))
    (hx : x ∈ sources)
    (trace : Trace a x (y + ((sources.filter (· < x)).length + 1)) xs) :
    MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r
      (y + ((sources.filter (· < x)).length + 1)) xs := by
  obtain ⟨left, right, hl, hrr, sourceGap, _, targetGap, below, hpy⟩ :=
    rankRealization_completion_geometry h hr hp hk hy hnt bounds gap beforeOwner packet
  exact completion_new_markTrace h.valid hr hs hk hy hl hrr sourceGap
    (fun z hz => lt_of_lt_of_le (below z hz) hpy) targetGap hx beforeOwner trace

/-- Local semantic geometry preserves any supplied old marked word, including
a word carrying a saved historical cutoff rather than its current cutoff. -/
theorem rankRealization_completion_preserves_markTrace {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r k y p nextTarget z : Nat} {row : Row}
    {sources xs : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (hs : sources.Nodup) (bounds : ∀ x ∈ sources, x ≤ a.length + 1)
    (gap : y + sources.length < nextTarget) (beforeOwner : y + sources.length < r)
    (packet : ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length))
    (old : MarkTrace a r z xs) :
    MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r z xs := by
  obtain ⟨left, right, hl, hrr, sourceGap, hdis, targetGap, below, hpy⟩ :=
    rankRealization_completion_geometry h hr hp hk hy hnt bounds gap beforeOwner packet
  obtain ⟨oldRow, j, source, hold, hm, hj, hjz, hjs, trace⟩ := old
  have he := Option.some.inj (hold.symm.trans hr)
  subst oldRow
  exact completion_old_markTrace h.valid hr ((h.proper r row hr).2 z hm).1 hm
    hj hjz hjs trace hs hdis targetGap
    (rankRealization_completion_old_intervals h hr hp hpy hj hjz hjs bounds beforeOwner targetGap packet)

end FullMarkedBLP


