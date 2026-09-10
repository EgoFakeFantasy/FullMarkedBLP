import FullMarkedBLP.ScanDirectAllCertificates
import FullMarkedBLP.CompletionEventRealization

namespace FullMarkedBLP

/-- Actual direct completion preserves the entire row realization. This is a
single entrance event; general words and intermediate-event geometry remain separate. -/
theorem scanRankReach_direct_realization {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (h : RankRowRealization a theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (ht : computeMarkTrace a r y = some [y, s]) :
    RankRowRealization (completeMark a rec r y) theta embedding := by
  have event := scanRankReach_direct_event_geometry reach entryRealization geometry h hr hm ht
  exact completionEvent_realization event hr hm
    (scanRankReach_direct_all_edges reach entryRealization geometry h hr hm ht)
    (scanRankReach_direct_all_certificates reach entryRealization geometry h hr hm ht)

end FullMarkedBLP
