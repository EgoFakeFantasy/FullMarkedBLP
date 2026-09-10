import FullMarkedBLP.CompletionGuard

namespace FullMarkedBLP

/-- States reached by the literal scan loop, without a fuel parameter. -/
inductive ScanReach (initial : Pattern) : Pattern → Records → Nat → Prop
  | start : ScanReach initial initial [] 1
  | next {a b rec r sources} : ScanReach initial a rec r → r ≤ a.length →
      native (completeFrozenMarks a rec r) r = some (b, sources) →
      ScanReach initial b (if sources.isEmpty then rec else (r, sources) :: rec)
        (r + sources.length + 1)

def RecordsBefore (r : Nat) (rec : Records) : Prop :=
  ∀ entry ∈ rec, 0 < entry.1 ∧ entry.1 < r ∧ entry.2 ≠ []

theorem scanReach_records_before {initial a : Pattern} {rec : Records} {r : Nat}
    (h : ScanReach initial a rec r) : 0 < r ∧ RecordsBefore r rec := by
  induction h with
  | start => exact ⟨by omega, by intro e he; simp at he⟩
  | @next a b rec r sources reach hbound hn ih =>
    refine ⟨by omega, ?_⟩
    intro entry he
    by_cases hs : sources = []
    · simp only [hs, List.isEmpty_nil, ↓reduceIte] at he
      obtain ⟨hp, hb, hne⟩ := ih.2 entry he
      exact ⟨hp, by omega, hne⟩
    · simp only [List.isEmpty_iff, hs, ↓reduceIte] at he
      rcases List.mem_cons.mp he with he | he
      · subst entry; exact ⟨ih.1, by omega, hs⟩
      · obtain ⟨hp, hb, hne⟩ := ih.2 entry he
        exact ⟨hp, by omega, hne⟩

theorem scanReach_records_ordered {initial a : Pattern} {rec : Records} {r : Nat}
    (h : ScanReach initial a rec r) : rec.Pairwise (fun x y => y.1 < x.1) := by
  induction h with
  | start => exact List.Pairwise.nil
  | @next a b rec r sources reach hbound hn ih =>
    by_cases hs : sources = []
    · simpa [hs] using ih
    · simp only [List.isEmpty_iff, hs, ↓reduceIte]
      apply List.pairwise_cons.mpr
      exact ⟨fun entry he => (scanReach_records_before reach).2 entry he |>.2.1, ih⟩

theorem scanReach_record_lookup_before {initial a : Pattern} {rec : Records} {r terminal : Nat}
    {sources : List Nat} (h : ScanReach initial a rec r)
    (hr : recordAt rec terminal = some sources) :
    0 < terminal ∧ terminal < r ∧ sources ≠ [] :=
  (scanReach_records_before h).2 (terminal, sources) (recordAt_mem hr)

/-- A fresh scan record does not shadow any previously stored row key. -/
theorem recordAt_push_preserves {rec : Records} {r old : Nat} {sources previous : List Nat}
    (hb : RecordsBefore r rec) (hr : recordAt rec old = some previous) :
    recordAt ((r, sources) :: rec) old = some previous := by
  have hh := hb (old, previous) (recordAt_mem hr)
  change ((List.find? (fun entry : Nat × List Nat => entry.1 == old) ((r, sources) :: rec)).map Prod.snd) = _
  rw [List.find?_cons_of_neg (by simpa using (show r ≠ old by omega))]
  exact hr

theorem scanFuel_reaches_end {fuel : Nat} {initial a result : Pattern} {rec : Records} {r : Nat}
    (reach : ScanReach initial a rec r) (h : scanFuel fuel a rec r = some result) :
    ∃ finalRec finalRow, ScanReach initial result finalRec finalRow ∧ result.length < finalRow := by
  induction fuel generalizing a rec r with
  | zero =>
    simp only [scanFuel] at h
    split at h
    next hb => cases Option.some.inj h; exact ⟨rec, r, reach, hb⟩
    next => simp at h
  | succ fuel ih =>
    simp only [scanFuel] at h
    split at h
    next hb => cases Option.some.inj h; exact ⟨rec, r, reach, hb⟩
    next hb =>
      obtain ⟨⟨b, sources⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
      exact ih (ScanReach.next reach (by omega) hn) h

theorem fullScan_reaches_end {a b : Pattern} (h : fullScan a = some b) :
    ∃ rec r, ScanReach a b rec r ∧ b.length < r ∧ RecordsBefore r rec := by
  obtain ⟨rec, r, reach, hb⟩ := scanFuel_reaches_end ScanReach.start h
  exact ⟨rec, r, reach, hb, (scanReach_records_before reach).2⟩

end FullMarkedBLP


