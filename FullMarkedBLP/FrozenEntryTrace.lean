import FullMarkedBLP.CopyTraceSat

namespace FullMarkedBLP

/-- Reflection through an unchanged prefix requires validity only before the edit. -/
theorem trace_reflect_prefix {a b : Pattern}
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    {s y bound : Nat} {xs : List Nat} (ht : Trace b s y xs) (hy : y < bound)
    (earlier : ∀ i, i < bound → rowAt b i = rowAt a i) : Trace a s y xs := by
  induction ht with
  | stop => exact Trace.stop
  | @next y z tail hsy hp ht ih =>
    have hp' : predecessor a y = some z := by
      simpa only [predecessor, earlier y hy] using hp
    have hz := predecessor_lt valid hp'
    exact Trace.next hsy hp' (ih (by omega))

theorem completion_sources_between_from_entry {initial a b : Pattern} {rec : Records} {r y : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r)
    (earlier : ∀ i, i < r → rowAt b i = rowAt a i) {row : Row} {sources : List Nat}
    (hr : rowAt b r = some row) (hm : y ∈ row.marks) (hy : y < r)
    (hc : completionRecord b rec r y = some sources) :
    ∃ k s xs, row.step ≤ k ∧ row.core[k]? = some y ∧
      row.core[k - row.step]? = some s ∧ Trace b s y xs ∧ Trace a s y xs ∧
      ∀ x ∈ sources, s < x ∧ x < y := by
  obtain ⟨xs, terminal, hxs, ht, hrec, _, _⟩ := completionRecord_iff.mp hc
  obtain ⟨old, k, s, ho, _, hk, hky, hks, htrace⟩ := computeMarkTrace_sound hr hm hxs
  have he := Option.some.inj (ho.symm.trans hr)
  subst old
  have hentry := trace_reflect_prefix valid htrace hy earlier
  have hfactor := trace_terminal_factor valid hentry ht
  have hrecord := recordAt_mem hrec
  refine ⟨k, s, xs, hk, hky, hks, htrace, hentry, ?_⟩
  intro x hx
  have hb := scanReach_record_sources_below historyValid reach hrecord x hx
  exact ⟨scanReach_record_above_predecessor historyValid reach hrecord hfactor.1 hx, by omega⟩

theorem completion_from_entry_preserves_later_marks {initial a b : Pattern} {rec : Records} {r y z : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r)
    (earlier : ∀ i, i < r → rowAt b i = rowAt a i) {row : Row}
    (hr : rowAt b r = some row) (hm : y ∈ row.marks) (hy : y < r)
    (hz : z ∈ row.marks) (hyz : y ≤ z) :
    ∃ nextRow, rowAt (completeMark b rec r y) r = some nextRow ∧ z ∈ nextRow.marks := by
  cases hc : completionRecord b rec r y with
  | none => exact ⟨row, by simp [completeMark, hr, hc], hz⟩
  | some sources =>
    obtain ⟨k, s, xs, _, _, _, _, _, hb⟩ := completion_sources_between_from_entry
      historyValid valid reach earlier hr hm hy hc
    refine ⟨completeMarkRow row y sources, ?_, ?_⟩
    · simpa only [completeMark, hr, hc] using (rowAt_set_self (new := completeMarkRow row y sources) hr)
    · exact completeMarkRow_preserves_later_marks hz hyz (fun x hx => (hb x hx).2)

theorem frozen_pending_marks_from_entry {initial a : Pattern} {rec : Records} {r : Nat} {row : Row}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) (hr : rowAt a r = some row)
    (sorted : row.marks.Pairwise (· < ·))
    (valid : ∀ i rw, rowAt a i = some rw → rw.CoreValid i)
    (marksBound : ∀ y ∈ row.marks, y < r)
    (processed pending : List Nat) (hsplit : processed ++ pending = row.marks) :
    ∀ z ∈ pending, ∃ currentRow,
      rowAt (processed.foldl (fun current y => completeMark current rec r y) a) r = some currentRow ∧
      z ∈ currentRow.marks := by
  induction processed using list_snoc_induction generalizing pending with
  | nil =>
    intro z hz
    exact ⟨row, hr, by simpa only [List.nil_append] using hsplit ▸ hz⟩
  | @step processed y ih =>
    have hsplit' : processed ++ (y :: pending) = row.marks := by simpa [List.append_assoc] using hsplit
    have hyp := ih (y :: pending) hsplit'
    obtain ⟨currentRow, hc, hym⟩ := hyp y (by simp)
    intro z hz
    obtain ⟨sameRow, hs, hzm⟩ := hyp z (by simp [hz])
    have he := Option.some.inj (hs.symm.trans hc)
    subst sameRow
    have hsorted : (y :: pending).Pairwise (· < ·) := by
      have hh : (processed ++ (y :: pending)).Pairwise (· < ·) := by simpa only [hsplit'] using sorted
      exact (List.pairwise_append.mp hh).2.1
    have hyz := (List.pairwise_cons.mp hsorted).1 z hz
    have hymem : y ∈ row.marks := by rw [← hsplit']; simp
    obtain ⟨nextRow, hn, hzn⟩ := completion_from_entry_preserves_later_marks historyValid
      valid reach
      (fun i hi => completeMarks_fold_other_row processed (by omega : i ≠ r)) hc hym (marksBound y hymem) hzm (by omega)
    exact ⟨nextRow, by simpa [List.foldl_append] using hn, hzn⟩


end FullMarkedBLP

