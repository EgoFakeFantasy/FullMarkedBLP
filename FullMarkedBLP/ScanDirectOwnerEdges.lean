import FullMarkedBLP.ScanRecordedWordPacket
import FullMarkedBLP.ScanBirthPacketEdges

namespace FullMarkedBLP

theorem scan_completion_direct_owner_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda}
    {theta : Nat → OrdinalDomain lambda} {rec : Records} {r y s : Nat} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanEmbeddingReach initial initialEmbedding a rec r embedding)
    (h : RankRowRealization a theta embedding)
    (ht : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources) :
    ∀ x ∈ sources, rankOrdinalAction (embedding y) (theta x) =
      theta (y + ((sources.filter (· < x)).length + 1)) := by
  exact scan_record_owner_edges historyValid reach h
    (recordAt_mem ((completionRecord_direct_iff ht).mp hc).1)

/-- Direct completion packet edges follow from their recorded birth values.
No realization of the current, still-being-verified pattern is assumed. -/
theorem scanRankReach_completion_direct_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y s : Nat} {sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entrances : ∀ before history owner oldTheta oldEmbedding,
      ScanRankReach initial initialTheta initialEmbedding before history owner oldTheta oldEmbedding → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (ht : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources) :
    ∀ x ∈ sources, rankOrdinalAction (embedding y) (theta x) =
      theta (y + ((sources.filter (· < x)).length + 1)) := by
  have hm := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
  have bounds := scanRankReach_record_source_bounds reach entrances hm
  intro x hx
  have edge := scanRankReach_record_edges reach hm (fun x hx => Nat.le_of_lt (bounds x hx)) x hx
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using edge

/-- A recorded direct factor inherits its saved weak agreement at the exact
new natural cutoff. Coverage refers to the saved cutoff, not the current one. -/
theorem scan_record_direct_natural_certificate {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda}
    {theta : Nat → OrdinalDomain lambda} {rec : Records} {r y offset : Nat}
    {sources : List Nat} (reach : ScanEmbeddingReach initial initialEmbedding a rec r embedding)
    (hm : (y, sources) ∈ rec) (hoff : offset ≤ sources.length)
    (owner : RankElementaryEmbedding lambda) {delta : Ordinal.{u}}
    (saved : rankCutoffAgreement delta owner (embedding y))
    (covered : (theta (y + offset + 1)).val ≤ delta) :
    naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta [y + offset] =
      some (theta (y + offset + 1)) ∧
    rankCutoffAgreement (theta (y + offset + 1)).val owner
      (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) [y + offset]) := by
  refine ⟨rfl, ?_⟩
  have factor := scanEmbeddingReach_records_agree reach y sources hm offset hoff
  intro x z hx hz
  simpa only [evalWord, factor] using saved x z (lt_of_lt_of_le hx covered) (lt_of_lt_of_le hz covered)

end FullMarkedBLP



