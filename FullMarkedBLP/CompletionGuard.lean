import FullMarkedBLP.CompletionPatternClosure

namespace FullMarkedBLP

theorem recordAt_mem {rec : Records} {r : Nat} {sources : List Nat}
    (h : recordAt rec r = some sources) : (r, sources) ∈ rec := by
  obtain ⟨entry, he, hv⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some he
  have hr := List.find?_some he
  have hr' : entry.1 = r := by simpa using hr
  have heq : entry = (r, sources) := Prod.ext hr' hv
  simpa only [heq] using hm

theorem currentPlusOne_iff {a : Pattern} {xs : List Nat} :
    currentPlusOne a xs = true ↔
    ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
      ∃ row, rowAt a parent = some row ∧ child + 1 ∈ row.core := by
  simp only [currentPlusOne, List.all_eq_true]
  constructor
  · intro h parent child hm
    have hh := h (parent, child) hm
    cases he : rowAt a parent with
    | none => simp [he] at hh
    | some row => exact ⟨row, rfl, by simpa [he] using hh⟩
  · intro h pair hm
    obtain ⟨row, hr, hc⟩ := h pair.1 pair.2 hm
    simpa [hr] using hc

theorem completionRecord_iff {a : Pattern} {rec : Records} {r y : Nat} {sources : List Nat} :
    completionRecord a rec r y = some sources ↔
    ∃ xs terminal, computeMarkTrace a r y = some xs ∧ fromRight xs 2 = some terminal ∧
      recordAt rec terminal = some sources ∧ sources ≠ [] ∧ currentPlusOne a xs = true := by
  constructor
  · intro h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨terminal, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ss, hs, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next => simp at h
    next hn =>
      split at h
      next hg =>
        cases Option.some.inj h
        exact ⟨xs, terminal, hxs, ht, hs, by simpa using hn, hg⟩
      next => simp at h
  · rintro ⟨xs, terminal, hxs, ht, hs, hn, hg⟩
    simp [completionRecord, hxs, ht, hs, hn, hg]

theorem completionRecord_sound {a : Pattern} {rec : Records} {r y : Nat}
    {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (h : completionRecord a rec r y = some sources) :
    ∃ xs terminal, MarkTrace a r y xs ∧ fromRight xs 2 = some terminal ∧
      (terminal, sources) ∈ rec ∧ sources ≠ [] ∧
      ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
        ∃ parentRow, rowAt a parent = some parentRow ∧ child + 1 ∈ parentRow.core := by
  obtain ⟨xs, terminal, hxs, ht, hs, hn, hg⟩ := completionRecord_iff.mp h
  exact ⟨xs, terminal, computeMarkTrace_sound hr hm hxs, ht, recordAt_mem hs, hn,
    currentPlusOne_iff.mp hg⟩

end FullMarkedBLP

