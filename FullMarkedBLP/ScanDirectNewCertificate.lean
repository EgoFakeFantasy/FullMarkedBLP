import FullMarkedBLP.ScanDirectNewMarkTrace
import FullMarkedBLP.ScanDirectOwnerEdges
import FullMarkedBLP.ScanDirectEndpointAgreement
import FullMarkedBLP.ScanCurrentRecordGap

namespace FullMarkedBLP

/-- Direct completion produces a full new marked certificate under explicit
saved-cutoff coverage and the local semantic packet/gap conditions. -/
theorem scan_completion_direct_new_certificate {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda}
    {theta : Nat → OrdinalDomain lambda} {rec : Records} {r : Nat}
    (reach : ScanEmbeddingReach initial initialEmbedding a rec r embedding)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (h : RankRowRealization a theta embedding)
    {k y p nextTarget s x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (ht : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources)
    (gap : y + sources.length < nextTarget)
    {delta : Ordinal.{u}} (saved : rankCutoffAgreement delta (embedding r) (embedding y))
    (hd : delta ≤ lambda)
    (endpointCoverage : (theta (y + sources.length + 1)).val ≤ delta)
    (hx : x ∈ sources) :
    ∃ xs newDelta,
      MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r
        (y + ((sources.filter (· < x)).length + 1)) xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some newDelta ∧
      newDelta.val ≤ delta ∧
      rankCutoffAgreement newDelta.val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  have hm := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  have beforeOwner := scanReach_record_targets_before (scanEmbeddingReach_forget reach) hm
  have rb := rowAt_bounds hr
  have coverage : ∀ z ∈ sources,
      (theta (y + ((sources.filter (· < z)).length + 1) + 1)).val ≤ delta := by
    intro z hz
    have rankz : (sources.filter (· < z)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨z, hz, by simp⟩
    by_cases heq : (sources.filter (· < z)).length + 1 = sources.length
    · simpa only [heq] using endpointCoverage
    · exact le_trans (h.increasing _ _ (by omega) (by omega)).le endpointCoverage
  have covered := coverage x hx
  have packet : ∀ z ∈ sources, rankOrdinalAction (embedding r) (theta z) =
      theta (y + 1 + (sources.filter (· < z)).length) := by
    intro z hz
    have rankz : (sources.filter (· < z)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨z, hz, by simp⟩
    have inc := h.increasing (y + ((sources.filter (· < z)).length + 1))
      (y + ((sources.filter (· < z)).length + 1) + 1) (by omega) (by omega)
    have visible : (theta (y + ((sources.filter (· < z)).length + 1))).val < delta :=
      lt_of_lt_of_le inc (coverage z hz)
    have edge := scan_completion_direct_owner_edges entrances reach h ht hc z hz
    have transferred := rankAgreement_reads_visible_target
      (fun u v hu hv => (saved u v hu hv).symm) hd visible edge
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using transferred
  have rank : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have cert := scan_record_direct_natural_certificate reach hm (by omega :
      (sources.filter (· < x)).length + 1 ≤ sources.length) (embedding r) saved covered
  refine ⟨[y + ((sources.filter (· < x)).length + 1), x],
    theta (y + ((sources.filter (· < x)).length + 1) + 1), ?_, ?_, covered, ?_⟩
  · exact scan_completion_direct_new_markTrace (scanEmbeddingReach_forget reach) entrances h
      hr hp hk hy hnt ht hc gap packet hx
  · exact cert.1
  · exact cert.2

/-- A direct event at the current scan entrance obtains its new certificate
from entry realization and prior geometry, with no separate saved cutoff input. -/
theorem scanRankReach_direct_new_certificate {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (h : RankRowRealization a theta embedding)
    {y s x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (ht : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources)
    (hx : x ∈ sources) :
    ∃ xs newDelta,
      MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r
        (y + ((sources.filter (· < x)).length + 1)) xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some newDelta ∧
      newDelta ≤ theta (y + sources.length + 1) ∧
      rankCutoffAgreement newDelta.val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  have valid := h.valid r row hr
  obtain ⟨k, hk, hy⟩ := (h.proper r row hr).2 y hm |>.2
  have stepBound := Row.step_lt_length valid.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  have index := (List.getElem?_eq_some_iff.mp hy).1
  have nextIndex : k + 1 < (row.full r).length := by simp [Row.full]; omega
  let nextTarget := (row.full r)[k + 1]
  have hnt : (row.full r)[k + 1]? = some nextTarget := List.getElem?_eq_getElem nextIndex
  have record := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  obtain ⟨ki, ky⟩ := List.getElem?_eq_some_iff.mp hy
  have fullY : (row.full r)[k]? = some y := by
    unfold Row.full
    rw [List.getElem?_append_left ki]
    exact hy
  obtain ⟨fi, fy⟩ := List.getElem?_eq_some_iff.mp fullY
  obtain ⟨ni, nt⟩ := List.getElem?_eq_some_iff.mp hnt
  have later := List.pairwise_iff_getElem.mp (coreValid_full_sorted (h.valid r row hr))
    k (k + 1) fi ni (by omega)
  rw [fy, nt] at later
  have gap := scanRankReach_current_record_gap reach hr record (List.mem_of_getElem? hnt) later
  have saved := scanRankReach_direct_endpoint_agreement reach entryRealization geometry hr hm ht hc
  have entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i := by
    intro before history owner prior bound
    obtain ⟨oldTheta, oldEmbedding, lifted⟩ := scanReach_rank_lift prior initialTheta initialEmbedding
    exact (geometry before history owner oldTheta oldEmbedding lifted bound).1
  exact scan_completion_direct_new_certificate (scanRankReach_embeddings reach) entrances h
    hr hp hk hy hnt ht hc gap saved (theta (y + sources.length + 1)).property.le (le_refl _) hx

end FullMarkedBLP





