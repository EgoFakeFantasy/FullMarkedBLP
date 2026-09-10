import FullMarkedBLP.ScanRankReach

namespace FullMarkedBLP

/-- Record edges follow from the actual native birth values and source bounds;
no current realization or global history-validity hypothesis is required. -/
theorem scanRankReach_record_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec)
    (bounds : ∀ x ∈ sources, x ≤ terminal) :
    ∀ x ∈ sources, rankOrdinalAction (embedding terminal) (theta x) =
      theta (terminal + 1 + (sources.filter (· < x)).length) := by
  obtain ⟨before, history, oldTheta, oldEmbedding, after, _, hn, he, hpre, targets⟩ :=
    scanRankReach_record_birth h hm
  intro x hx
  have hk : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  rw [he, hpre x (bounds x hx), targets _ hk]
  exact (nativeFreshValues_at_source_rank oldTheta (oldEmbedding terminal)
    (native_sources_of_success hn) hx).symm

/-- It suffices to validate native entrances to discharge those source bounds. -/
theorem scanRankReach_record_source_bounds {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entrances : ∀ before history owner oldTheta oldEmbedding,
      ScanRankReach initial initialTheta initialEmbedding before history owner oldTheta oldEmbedding → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) :
    ∀ x ∈ sources, x < terminal := by
  obtain ⟨before, history, oldTheta, oldEmbedding, after, reach, hn, _⟩ :=
    scanRankReach_record_birth h hm
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  exact nativeSources_below_owner (entrances before history terminal oldTheta oldEmbedding reach
    ((scanReach_records_before (scanEmbeddingReach_forget (scanRankReach_embeddings h))).2
      (terminal, sources) hm).2.1)
    hr (native_sources_of_success hn)

/-- Whole-word packet images retain the same reduced assumptions. -/
theorem scanRankReach_record_word_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec)
    (bounds : ∀ x ∈ sources, x ≤ terminal) (front : List Nat) :
    ∀ x ∈ sources, rankOrdinalAction (rankWordEmbedding embedding (front ++ [terminal])) (theta x) =
      evalWord (fun i => rankOrdinalAction (embedding i)) front
        (theta (terminal + 1 + (sources.filter (· < x)).length)) := by
  intro x hx
  rw [rankWordEmbedding_ordinalAction, evalWord_append]
  simp only [evalWord]
  rw [scanRankReach_record_edges h hm bounds x hx]

end FullMarkedBLP

