import FullMarkedBLP.DirectPacketBounds

namespace FullMarkedBLP

theorem fromRight_cons_of_le {xs : List Nat} {y k : Nat} (hk : k ≤ xs.length) :
    fromRight (y :: xs) k = fromRight xs k := by
  by_cases hz : k = 0
  · subst k; simp [fromRight]
  · have he : xs.length + 1 - k = (xs.length - k) + 1 := by omega
    simp [fromRight, show 0 < k by omega, hk, show k ≤ xs.length + 1 by omega, he]

/-- The last word factor points exactly to the trace endpoint. -/
theorem trace_terminal_factor {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s y terminal : Nat} {xs : List Nat} (ht : Trace a s y xs)
    (hf : fromRight xs 2 = some terminal) :
    predecessor a terminal = some s ∧ s < terminal ∧ terminal ≤ y := by
  induction ht with
  | stop => simp [fromRight] at hf
  | @next y z tail hsy hp ht ih =>
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons v rest =>
      cases rest with
      | nil =>
        have hv : v = z := by simpa using trace_head ht
        have hs : v = s := by simpa using trace_last ht
        have hy : y = terminal := by simpa [fromRight] using hf
        subst terminal
        exact ⟨by simpa only [← hv, hs] using hp, hsy, Nat.le_refl y⟩
      | cons w rest =>
        have hf' : fromRight (v :: w :: rest) 2 = some terminal := by
          simpa only [fromRight_cons_of_le (by simp : 2 ≤ (v :: w :: rest).length)] using hf
        have hh := ih hf'
        have hz := predecessor_lt valid hp
        exact ⟨hh.1, hh.2.1, by omega⟩

/-- Every successful marked completion reads sources between its old endpoint
and target, for words of arbitrary length. -/
theorem completion_sources_between {initial a : Pattern} {rec : Records} {r y : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources) :
    ∃ k s xs, row.step ≤ k ∧ row.core[k]? = some y ∧
      row.core[k - row.step]? = some s ∧ Trace a s y xs ∧
      ∀ x ∈ sources, s < x ∧ x < y := by
  obtain ⟨xs, terminal, hxs, ht, hrec, _, _⟩ := completionRecord_iff.mp hc
  obtain ⟨old, k, s, ho, _, hk, hky, hks, htrace⟩ := computeMarkTrace_sound hr hm hxs
  have he := Option.some.inj (ho.symm.trans hr)
  subst old
  have hfactor := trace_terminal_factor valid htrace ht
  have hrecord := recordAt_mem hrec
  refine ⟨k, s, xs, hk, hky, hks, htrace, ?_⟩
  intro x hx
  have hb := scanReach_record_sources_below historyValid reach hrecord x hx
  exact ⟨scanReach_record_above_predecessor historyValid reach hrecord hfactor.1 hx, by omega⟩

theorem completion_preserves_later_marks {initial a : Pattern} {rec : Records} {r y z : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) {row : Row}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hz : z ∈ row.marks) (hyz : y ≤ z) :
    ∃ nextRow, rowAt (completeMark a rec r y) r = some nextRow ∧ z ∈ nextRow.marks := by
  cases hc : completionRecord a rec r y with
  | none => exact ⟨row, by simpa [completeMark, hr, hc] using hr, hz⟩
  | some sources =>
    obtain ⟨k, s, xs, _, _, _, _, hb⟩ := completion_sources_between historyValid valid reach hr hm hc
    refine ⟨completeMarkRow row y sources, ?_, ?_⟩
    · simpa only [completeMark, hr, hc] using (rowAt_set_self (new := completeMarkRow row y sources) hr)
    · exact completeMarkRow_preserves_later_marks hz hyz (fun x hx => (hb x hx).2)

end FullMarkedBLP


