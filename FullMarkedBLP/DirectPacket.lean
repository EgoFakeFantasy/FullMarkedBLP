import FullMarkedBLP.ScanPrefix

namespace FullMarkedBLP

theorem completionRecord_direct_iff {a : Pattern} {rec : Records} {r y s : Nat}
    {sources : List Nat} (htrace : computeMarkTrace a r y = some [y, s]) :
    completionRecord a rec r y = some sources ↔ recordAt rec y = some sources ∧ sources ≠ [] := by
  rw [completionRecord_iff]
  constructor
  · rintro ⟨xs, terminal, hxs, ht, hr, hn, _⟩
    have he := Option.some.inj (hxs.symm.trans htrace)
    subst xs
    have ht' : y = terminal := by simpa [fromRight] using ht
    subst terminal
    exact ⟨hr, hn⟩
  · rintro ⟨hr, hn⟩
    exact ⟨[y, s], y, htrace, by simp [fromRight], hr, hn, by simp [currentPlusOne]⟩

/-- For a direct word, the entire packet is already present in the scanned prefix. -/
theorem completion_direct_packet {initial a : Pattern} {rec : Records} {r y s : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {sources : List Nat}
    (htrace : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources) :
    sources.Nodup ∧ y + sources.length < r ∧
      ∀ x ∈ sources, Trace a x (y + ((sources.filter (· < x)).length + 1))
        [y + ((sources.filter (· < x)).length + 1), x] := by
  have hr := ((completionRecord_direct_iff htrace).mp hc).1
  have hm := recordAt_mem hr
  exact ⟨scanReach_completion_sources_nodup historyValid reach hc,
    scanReach_record_targets_before reach hm,
    fun x hx => scanReach_record_trace historyValid reach hm hx⟩

theorem scanReach_record_above_predecessor {initial a : Pattern} {rec : Records} {r : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {terminal p x : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) (hp : predecessor a terminal = some p)
    (hx : x ∈ sources) : p < x := by
  induction reach with
  | start => simp at hm
  | @next before after history owner ss previous hb hn ih =>
    have preserve : (terminal, sources) ∈ history → p < x := by
      intro he
      have ht := (scanReach_records_before previous).2 (terminal, sources) he
      have hp' : predecessor before terminal = some p := by
        simpa only [predecessor, scan_step_prefix_rowAt hn ht.2.1] using hp
      exact ih he hp'
    by_cases hs : ss = []
    · simp only [hs, List.isEmpty_nil, ↓reduceIte] at hm
      exact preserve hm
    · simp only [List.isEmpty_iff, hs, ↓reduceIte] at hm
      rcases List.mem_cons.mp hm with he | he
      · obtain ⟨he1, he2⟩ := Prod.mk.inj he
        subst terminal
        subst sources
        have valid := historyValid before history owner previous
        have hss := native_sources_of_success hn
        obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
        have hv := valid owner row hr
        have hl := Row.step_lt_length hv.2.2.2
        obtain ⟨q, hq⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
        have hqp : row.p = some q := hq
        have hpred : predecessor (completeFrozenMarks before history owner) owner = some q := by
          simp only [predecessor, hr, Option.bind_some, hqp]
        have hout := native_owner_predecessor valid hn hpred
        have heq := Option.some.inj (hout.symm.trans hp)
        subst p
        exact nativeSources_above_p valid hr hqp hss x hx
      · exact preserve he

end FullMarkedBLP

