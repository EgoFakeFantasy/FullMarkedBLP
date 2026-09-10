import FullMarkedBLP.DirectPacket

namespace FullMarkedBLP

theorem trace_two_predecessor {a : Pattern} {source y s : Nat}
    (h : Trace a source y [y, s]) : source = s ∧ predecessor a y = some s := by
  have he : s = source := by simpa using trace_last h
  subst source
  cases h with
  | next hlt hp ht =>
    have hh := trace_head ht
    have hz := Option.some.inj hh
    exact ⟨rfl, by simpa only [← hz] using hp⟩

theorem computeMarkTrace_direct_predecessor {a : Pattern} {r y s : Nat} {row : Row}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (ht : computeMarkTrace a r y = some [y, s]) : predecessor a y = some s := by
  obtain ⟨_, _, _, _, _, _, _, _, htrace⟩ := computeMarkTrace_sound hr hm ht
  exact (trace_two_predecessor htrace).2

theorem completion_direct_source_bounds {initial a : Pattern} {rec : Records} {r y s : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (htrace : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources) :
    ∀ x ∈ sources, s < x ∧ x < y := by
  have hrecord := recordAt_mem ((completionRecord_direct_iff htrace).mp hc).1
  have hp := computeMarkTrace_direct_predecessor hr hm htrace
  intro x hx
  exact ⟨scanReach_record_above_predecessor historyValid reach hrecord hp hx,
    scanReach_record_sources_below historyValid reach hrecord x hx⟩

theorem completeMarkRow_preserves_later_marks {row : Row} {y z : Nat} {sources : List Nat}
    (hz : z ∈ row.marks) (hyz : y ≤ z) (hbelow : ∀ x ∈ sources, x < y) :
    z ∈ (completeMarkRow row y sources).marks := by
  have hnm : z ∉ sources := by intro hx; have hh := hbelow z hx; omega
  simp only [completeMarkRow, mem_canonicalColumns, List.mem_append, List.mem_filter]
  exact Or.inl ⟨hz, by simp [hnm]⟩

theorem completion_direct_preserves_later_marks {initial a : Pattern} {rec : Records} {r y s z : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (htrace : computeMarkTrace a r y = some [y, s])
    (hc : completionRecord a rec r y = some sources)
    (hz : z ∈ row.marks) (hyz : y ≤ z) :
    ∃ nextRow, rowAt (completeMark a rec r y) r = some nextRow ∧ z ∈ nextRow.marks := by
  have hb := completion_direct_source_bounds historyValid reach hr hm htrace hc
  refine ⟨completeMarkRow row y sources, ?_, ?_⟩
  · simpa only [completeMark, hr, hc] using (rowAt_set_self (new := completeMarkRow row y sources) hr)
  · exact completeMarkRow_preserves_later_marks hz hyz (fun x hx => (hb x hx).2)

end FullMarkedBLP


