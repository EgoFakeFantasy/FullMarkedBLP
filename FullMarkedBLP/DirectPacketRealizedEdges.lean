import FullMarkedBLP.WordPacketEdgeTransfer
import FullMarkedBLP.DirectPacketBounds

namespace FullMarkedBLP

theorem realized_two_trace_edge {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {x y : Nat}
    (ht : Trace a x y [y, x]) : rankOrdinalAction (embedding y) (theta x) = theta y := by
  have hp := (trace_two_predecessor ht).2
  obtain ⟨row, hr, he⟩ := Option.bind_eq_some_iff.mp hp
  exact realizesEdges_p (h.valid y row hr) (h.edges y row hr) he

theorem realized_completion_direct_packet_edges {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y s : Nat} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (h : RankRowRealization a theta embedding)
    (ht : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources) :
    ∀ x ∈ sources,
      rankOrdinalAction (embedding (y + ((sources.filter (· < x)).length + 1))) (theta x) =
        theta (y + ((sources.filter (· < x)).length + 1)) := by
  intro x hx
  exact realized_two_trace_edge h ((completion_direct_packet historyValid reach ht hc).2.2 x hx)

end FullMarkedBLP
