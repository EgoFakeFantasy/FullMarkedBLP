import FullMarkedBLP.ScanFrozenHistoricalCoverage

namespace FullMarkedBLP

/-- A penultimate factor determines the exact final two entries of the word. -/
theorem fromRight_two_decomposition {xs : List Nat} {terminal : Nat}
    (h : fromRight xs 2 = some terminal) :
    ∃ front last, xs = front ++ [terminal, last] := by
  induction xs using List.reverseRecOn with
  | nil => simp [fromRight] at h
  | @append_singleton rest last _ =>
    induction rest using List.reverseRecOn with
    | nil => simp [fromRight] at h
    | @append_singleton front penultimate _ =>
      have eq : penultimate = terminal := by
        simpa [fromRight, List.getElem?_append] using h
      subst penultimate
      exact ⟨front, last, by simp [List.append_assoc]⟩

theorem scanRankReach_frozen_recorded_word_coverage {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j)
    (processed : List Nat)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (valid : ∀ i rw,
      rowAt (processed.foldl (fun current z => completeMark current rec r z) a) i = some rw → rw.CoreValid i)
    {current : Row} (hr : rowAt a r = some current)
    {y : Nat} {sources : List Nat} (hm : y ∈ current.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∃ (front : List Nat) (terminal last : Nat) (delta : OrdinalDomain lambda),
      computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y =
        some (front ++ [terminal, last]) ∧
      recordAt rec terminal = some sources ∧
      rankCutoffAgreement delta.val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) (front ++ [terminal])) ∧
      ∀ k, k < sources.length →
        evalWord (fun i => rankOrdinalAction (embedding i)) front (theta (terminal + 1 + k)) < delta := by
  obtain ⟨phi, mono, holds, records, certs⟩ :=
    scanRankReach_frozen_historical_coverage h entryRealization geometry increasing processed events valid hr
  obtain ⟨xs, delta, _, computed, cutoff, saved⟩ := certs y hm
  obtain ⟨word, terminal, currentComputed, terminalAt, record, _, _⟩ := completionRecord_iff.mp hc
  have eq := Option.some.inj (currentComputed.symm.trans computed)
  subst word
  rw [fromRight_map] at terminalAt
  obtain ⟨v, hv, mapped⟩ := Option.map_eq_some_iff.mp terminalAt
  obtain ⟨front, last, shape⟩ := fromRight_two_decomposition hv
  obtain ⟨i, hi, _, covered⟩ := records terminal sources (recordAt_mem record)
  have same : i = v := mono.injective (hi.trans mapped.symm)
  subst i
  have cutoff' : naturalCutoff (fun i => rankOrdinalAction (initialEmbedding i)) initialTheta
      (front ++ [v]) = some delta := by
    simpa [shape] using cutoff
  refine ⟨front.map phi, terminal, phi last, delta, ?_, record, ?_, ?_⟩
  · simpa [shape, List.map_append, mapped] using computed
  · simpa [shape, List.map_append, mapped] using saved
  · exact covered front delta cutoff'
end FullMarkedBLP


