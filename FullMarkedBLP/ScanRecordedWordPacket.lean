import FullMarkedBLP.ScanEmbeddingReach
import FullMarkedBLP.ScanRecordedPredecessorPrior

namespace FullMarkedBLP

/-- Every retained record supplies terminal-owner edges, independently of which
current mark reads it. -/
theorem scan_record_owner_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda}
    {theta : Nat → OrdinalDomain lambda} {rec : Records} {r terminal : Nat} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanEmbeddingReach initial initialEmbedding a rec r embedding)
    (h : RankRowRealization a theta embedding) (hm : (terminal, sources) ∈ rec) :
    ∀ x ∈ sources, rankOrdinalAction (embedding terminal) (theta x) =
      theta (terminal + ((sources.filter (· < x)).length + 1)) := by
  intro x hx
  have he := realized_two_trace_edge h
    (scanReach_record_trace_prior (scanEmbeddingReach_forget reach) historyValid hm hx)
  have hk : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  rw [scanEmbeddingReach_records_agree reach terminal sources hm _ (by omega)] at he
  exact he

/-- Actual retained terminal packets propagate through any whole word. -/
theorem scan_record_word_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda}
    {theta : Nat → OrdinalDomain lambda} {rec : Records} {r terminal : Nat} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanEmbeddingReach initial initialEmbedding a rec r embedding)
    (h : RankRowRealization a theta embedding) (hm : (terminal, sources) ∈ rec)
    (front : List Nat) :
    ∀ x ∈ sources, rankOrdinalAction (rankWordEmbedding embedding (front ++ [terminal])) (theta x) =
      evalWord (fun i => rankOrdinalAction (embedding i)) front
        (theta (terminal + ((sources.filter (· < x)).length + 1))) := by
  intro x hx
  rw [rankWordEmbedding_ordinalAction, evalWord_append]
  simp only [evalWord]
  rw [scan_record_owner_edges historyValid reach h hm x hx]

/-- Transfer of the current retained packet requires strict coverage by the
historical cutoff; current natural-cutoff coverage is not assumed. -/
theorem scan_record_word_packet_transfer {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda}
    {theta : Nat → OrdinalDomain lambda} {rec : Records} {r terminal : Nat} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanEmbeddingReach initial initialEmbedding a rec r embedding)
    (h : RankRowRealization a theta embedding) (hm : (terminal, sources) ∈ rec)
    (front : List Nat) (owner : RankElementaryEmbedding lambda) {delta : Ordinal.{u}}
    (hd : delta ≤ lambda)
    (hc : rankCutoffAgreement delta (rankWordEmbedding embedding (front ++ [terminal])) owner)
    (covered : ∀ x ∈ sources,
      (evalWord (fun i => rankOrdinalAction (embedding i)) front
        (theta (terminal + ((sources.filter (· < x)).length + 1)))).val < delta) :
    ∀ x ∈ sources, rankOrdinalAction owner (theta x) =
      evalWord (fun i => rankOrdinalAction (embedding i)) front
        (theta (terminal + ((sources.filter (· < x)).length + 1))) := by
  intro x hx
  exact rankAgreement_reads_visible_target hc hd (covered x hx)
    (scan_record_word_edges historyValid reach h hm front x hx)

end FullMarkedBLP


