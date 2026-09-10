import FullMarkedBLP.WordPacketCoverage

namespace FullMarkedBLP

theorem word_packet_edge_transfer {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r p e x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (hx : x ∈ sources)
    (front : List Nat) (owner : RankElementaryEmbedding lambda) {delta : OrdinalDomain lambda}
    (hd : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta (front ++ [r]) = some delta)
    (hc : rankCutoffAgreement delta.val (rankWordEmbedding embedding (front ++ [r])) owner) :
    rankOrdinalAction owner (theta x) =
      evalWord (fun i => rankOrdinalAction (embedding i)) front
        (nativeFreshValues theta (embedding r) r sources (sources.filter (· < x)).length) := by
  apply rankAgreement_reads_visible_target hc delta.property.le
  · exact native_packet_word_target_covered h hr hp he hs front hd _
  · rw [rankWordEmbedding_ordinalAction, evalWord_append]
    simp only [evalWord]
    rw [nativeFreshValues_at_source_rank theta (embedding r) hs hx]

end FullMarkedBLP
