import FullMarkedBLP.ScanRecordHistoricalCoverage
import FullMarkedBLP.ScanBirthPacketEdges

namespace FullMarkedBLP

/-- A whole-word packet has genuine edge equations and is strictly below the
current prefix image of its witnessed birth successor. Equality of this bound
with a saved entrance certificate is a separate obligation. Only earlier
native entrances are used here. -/
theorem scanRankReach_word_birth_packet {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entrances : ∀ before history owner oldTheta oldEmbedding,
      ScanRankReach initial initialTheta initialEmbedding before history owner oldTheta oldEmbedding →
      owner < r → RankRowRealization (completeFrozenMarks before history owner) oldTheta oldEmbedding)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) (front : List Nat) :
    ∃ before history oldTheta oldEmbedding after,
      ScanRankReach initial initialTheta initialEmbedding before history terminal oldTheta oldEmbedding ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) ∧
      ∀ x ∈ sources,
        rankOrdinalAction (rankWordEmbedding embedding (front ++ [terminal])) (theta x) =
          evalWord (fun i => rankOrdinalAction (embedding i)) front
            (theta (terminal + 1 + (sources.filter (· < x)).length)) ∧
        evalWord (fun i => rankOrdinalAction (embedding i)) front
            (theta (terminal + 1 + (sources.filter (· < x)).length)) <
          evalWord (fun i => rankOrdinalAction (embedding i)) front (oldTheta (terminal + 1)) := by
  obtain ⟨before, history, oldTheta, oldEmbedding, after, reach, hn, covered⟩ :=
    scanRankReach_record_historical_coverage h entrances hm
  have bounds := scanRankReach_record_source_bounds h
    (fun before history owner oldTheta oldEmbedding reach hb =>
      (entrances before history owner oldTheta oldEmbedding reach hb).valid) hm
  refine ⟨before, history, oldTheta, oldEmbedding, after, reach, hn, ?_⟩
  intro x hx
  have hk : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  exact ⟨scanRankReach_record_word_edges h hm (fun x hx => (bounds x hx).le) front x hx,
    rankWord_strictMono embedding front (covered _ hk)⟩

end FullMarkedBLP
