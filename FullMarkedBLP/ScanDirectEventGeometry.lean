import FullMarkedBLP.ScanDirectOwnerPacket
import FullMarkedBLP.ScanCurrentRecordGap
import FullMarkedBLP.CompletionEventEdges

namespace FullMarkedBLP

/-- All local event-geometry obligations hold for a direct mark at the actual
scan entrance, from the entry/current realizations and prior geometry. -/
theorem scanRankReach_direct_event_geometry {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (h : RankRowRealization a theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (ht : computeMarkTrace a r y = some [y, s]) :
    CompletionEventGeometry a rec r y theta embedding := by
  refine ⟨h, ?_⟩
  intro other sources hother hc
  have he := Option.some.inj (hother.symm.trans hr)
  subst other
  have valid := h.valid r row hr
  obtain ⟨k, hk, hy⟩ := (h.proper r row hr).2 y hm |>.2
  have stepBound := Row.step_lt_length valid.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  have index := (List.getElem?_eq_some_iff.mp hy).1
  have nextIndex : k + 1 < (row.full r).length := by simp [Row.full]; omega
  let nextTarget := (row.full r)[k + 1]
  have hnt : (row.full r)[k + 1]? = some nextTarget := List.getElem?_eq_getElem nextIndex
  have record := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  have unlabelled := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  have beforeOwner := scanReach_record_targets_before unlabelled record
  have sourceBounds := scanRankReach_record_source_bounds reach
    (fun before history owner oldTheta oldEmbedding prior bound =>
      (geometry before history owner oldTheta oldEmbedding prior bound).1) record
  have rb := rowAt_bounds hr
  have fullY : (row.full r)[k]? = some y := by
    unfold Row.full
    rw [List.getElem?_append_left index]
    exact hy
  obtain ⟨fi, fy⟩ := List.getElem?_eq_some_iff.mp fullY
  obtain ⟨ni, nt⟩ := List.getElem?_eq_some_iff.mp hnt
  have later := List.pairwise_iff_getElem.mp (coreValid_full_sorted valid) k (k + 1) fi ni (by omega)
  rw [fy, nt] at later
  refine ⟨k, p, nextTarget, hp, hk, hy, hnt, scanReach_record_nodup unlabelled record,
    ?_, scanRankReach_current_record_gap reach hr record (List.mem_of_getElem? hnt) later,
    beforeOwner, scanRankReach_direct_owner_packet reach entryRealization geometry h.increasing hr hm ht hc⟩
  intro x hx
  have bound := sourceBounds x hx
  omega

/-- Actual direct entrance completion preserves all row edges, including
long-row edges, using only entry/current realization and prior geometry. -/
theorem scanRankReach_direct_all_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (h : RankRowRealization a theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (ht : computeMarkTrace a r y = some [y, s]) :
    ∀ i out, rowAt (completeMark a rec r y) i = some out →
      out.RealizesEdges (rankOrdinalAction (embedding i)) theta i := by
  have entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i := by
    intro before history owner prior bound
    obtain ⟨oldTheta, oldEmbedding, lifted⟩ := scanReach_rank_lift prior initialTheta initialEmbedding
    exact (geometry before history owner oldTheta oldEmbedding lifted bound).1
  exact completionEvent_reachable_all_edges entrances
    (scanEmbeddingReach_forget (scanRankReach_embeddings reach))
    (scanRankReach_direct_event_geometry reach entryRealization geometry h hr hm ht) hr hm
end FullMarkedBLP

