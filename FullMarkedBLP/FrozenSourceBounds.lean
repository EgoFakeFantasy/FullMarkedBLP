import FullMarkedBLP.CompletionSourceBounds

namespace FullMarkedBLP

theorem completion_sources_between_in_prefix {initial a b : Pattern} {rec : Records} {r y : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ i row, rowAt b i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r)
    (earlier : ∀ i, i < r → rowAt b i = rowAt a i) {row : Row} {sources : List Nat}
    (hr : rowAt b r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord b rec r y = some sources) :
    ∃ k s xs, row.step ≤ k ∧ row.core[k]? = some y ∧
      row.core[k - row.step]? = some s ∧ Trace b s y xs ∧
      ∀ x ∈ sources, s < x ∧ x < y := by
  obtain ⟨xs, terminal, hxs, ht, hrec, _, _⟩ := completionRecord_iff.mp hc
  obtain ⟨old, k, s, ho, _, hk, hky, hks, htrace⟩ := computeMarkTrace_sound hr hm hxs
  have he := Option.some.inj (ho.symm.trans hr)
  subst old
  have hfactor := trace_terminal_factor valid htrace ht
  have hrecord := recordAt_mem hrec
  have hterminal := (scanReach_records_before reach).2 (terminal, sources) hrecord
  have hp : predecessor a terminal = some s := by
    simpa only [predecessor, earlier terminal hterminal.2.1] using hfactor.1
  refine ⟨k, s, xs, hk, hky, hks, htrace, ?_⟩
  intro x hx
  have hb := scanReach_record_sources_below historyValid reach hrecord x hx
  exact ⟨scanReach_record_above_predecessor historyValid reach hrecord hp hx, by omega⟩


/-- The source bounds hold after any actual prefix of the frozen fold. -/
theorem frozen_completion_sources_between {initial a : Pattern} {rec : Records} {r y : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) (processed : List Nat)
    (valid : ∀ i row, rowAt (processed.foldl (fun current z => completeMark current rec r z) a) i = some row → row.CoreValid i)
    {row : Row} {sources : List Nat}
    (hr : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some row)
    (hm : y ∈ row.marks)
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    ∃ k s xs, row.step ≤ k ∧ row.core[k]? = some y ∧
      row.core[k - row.step]? = some s ∧
      Trace (processed.foldl (fun current z => completeMark current rec r z) a) s y xs ∧
      ∀ x ∈ sources, s < x ∧ x < y := by
  exact completion_sources_between_in_prefix historyValid valid reach
    (fun i hi => completeMarks_fold_other_row processed (by omega : i ≠ r)) hr hm hc

end FullMarkedBLP


