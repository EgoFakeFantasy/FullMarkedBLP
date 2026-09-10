import FullMarkedBLP.ScanCurrentHistoricalCertificates

namespace FullMarkedBLP

/-- For an actual direct entry completion, the saved agreement is available
at exactly the record's endpoint successor, with no separate coverage input. -/
theorem scanRankReach_direct_endpoint_agreement {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y s : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    {row : Row} {sources : List Nat} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (ht : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources) :
    rankCutoffAgreement (theta (y + sources.length + 1)).val (embedding r) (embedding y) := by
  obtain ⟨phi, hmono, holds, records, certs⟩ :=
    scanRankReach_current_historical_certificates h entryRealization geometry hr
  obtain ⟨xs, delta, _, computed, cutoff, saved⟩ := certs y hm
  have word : xs.map phi = [y, s] := Option.some.inj (computed.symm.trans ht)
  have length : xs.length = 2 := by have hh := congrArg List.length word; simpa using hh
  cases xs with
  | nil => simp at length
  | cons v rest =>
    cases rest with
    | nil => simp at length
    | cons w rest =>
      have empty : rest = [] := by cases rest <;> simp_all
      subst rest
      have mapped : phi v = y := by simpa using congrArg List.head? word
      have deltaeq : initialTheta (v + 1) = delta := by simpa [naturalCutoff] using cutoff
      have record := recordAt_mem ((completionRecord_direct_iff ht).mp hc).1
      obtain ⟨i, hi, hn⟩ := records y sources record
      have hiv : i = v := hmono.injective (hi.trans mapped.symm)
      subst i
      have endpoint : theta (y + sources.length + 1) = delta := by
        rw [← hn, (holds (v + 1)).1, deltaeq]
      rw [endpoint]
      simpa [evalWord, mapped] using saved

end FullMarkedBLP

