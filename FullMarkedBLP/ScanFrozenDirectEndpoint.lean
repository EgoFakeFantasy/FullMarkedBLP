import FullMarkedBLP.ScanDirectEndpointAgreement
import FullMarkedBLP.FrozenHistoricalTrace
import FullMarkedBLP.MarkTraceIdentification

namespace FullMarkedBLP

/-- A still-frozen original mark keeps its recorded endpoint agreement at an
intermediate completion state. The successful direct word is identified with
the transported historical word rather than assumed at the entrance. -/
theorem scanRankReach_frozen_direct_endpoint_agreement {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row currentRow : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (currentRowAt : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some currentRow)
    (sorted : currentRow.core.Pairwise (· < ·))
    (ht : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some [y, s])
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    rankCutoffAgreement (theta (y + sources.length + 1)).val (embedding r) (embedding y) := by
  obtain ⟨phi, _, _, _, certs⟩ :=
    scanRankReach_current_historical_certificates reach entryRealization geometry hr
  obtain ⟨xs, delta, oldTrace, oldComputed, _, _⟩ := certs y hm
  have transported := frozen_fold_preserves_historical_trace processed events oldTrace
  have identified := computeMarkTrace_identify currentRowAt sorted transported ht
  have originalComputed : computeMarkTrace a r y = some [y, s] := by
    simpa only [← identified] using oldComputed
  have originalRecord : completionRecord a rec r y = some sources :=
    (completionRecord_direct_iff originalComputed).mpr ((completionRecord_direct_iff ht).mp hc)
  exact scanRankReach_direct_endpoint_agreement reach entryRealization geometry hr hm originalComputed originalRecord

end FullMarkedBLP
