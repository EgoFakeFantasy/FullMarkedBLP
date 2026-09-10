import FullMarkedBLP.ScanRecords

namespace FullMarkedBLP

/-- A historical record is witnessed by an actual earlier native event. -/
theorem scanReach_record_origin {initial a : Pattern} {rec : Records} {r : Nat}
    (reach : ScanReach initial a rec r) {terminal : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) :
    ∃ before after history, ScanReach initial before history terminal ∧
      terminal ≤ before.length ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) := by
  induction reach with
  | start => simp at hm
  | @next before after history owner ss previous hb hn ih =>
    by_cases hs : ss = []
    · simp only [hs, List.isEmpty_nil, ↓reduceIte] at hm
      exact ih hm
    · simp only [List.isEmpty_iff, hs, ↓reduceIte] at hm
      rcases List.mem_cons.mp hm with he | he
      · obtain ⟨he1, he2⟩ := Prod.mk.inj he
        subst terminal
        subst sources
        exact ⟨before, after, history, previous, hb, hn⟩
      · exact ih he

theorem native_sources_of_success {a b : Pattern} {r : Nat} {sources : List Nat}
    (h : native a r = some (b, sources)) : nativeSources a r = some sources := by
  obtain ⟨row, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ss, hs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨block, _, h⟩ := Option.bind_eq_some_iff.mp h
  change some (_, ss) = some (b, sources) at h
  have he := congrArg Prod.snd (Option.some.inj h)
  change ss = sources at he
  simpa only [he] using hs

/-- Source order follows from core validity at the historical event, rather
than an unsupported assertion about the current modified rows. -/
theorem scanReach_record_decreasing {initial a : Pattern} {rec : Records} {r : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {terminal : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) : sources.Pairwise (· > ·) := by
  obtain ⟨before, after, history, previous, _, hn⟩ := scanReach_record_origin reach hm
  exact nativeSources_decreasing (historyValid before history terminal previous)
    (native_sources_of_success hn)

theorem scanReach_completion_sources_nodup {initial a : Pattern} {rec : Records} {r y : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {sources : List Nat}
    (hc : completionRecord a rec r y = some sources) : sources.Nodup := by
  obtain ⟨xs, terminal, _, _, hr, _, _⟩ := completionRecord_iff.mp hc
  exact (scanReach_record_decreasing historyValid reach (recordAt_mem hr)).imp
    (fun h => Nat.ne_of_gt h)

theorem scanReach_record_sources_below {initial a : Pattern} {rec : Records} {r : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {terminal : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) : ∀ x ∈ sources, x < terminal := by
  obtain ⟨before, after, history, previous, _, hn⟩ := scanReach_record_origin reach hm
  have hs := native_sources_of_success hn
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  exact nativeSources_below_owner (historyValid before history terminal previous) hr hs

end FullMarkedBLP


