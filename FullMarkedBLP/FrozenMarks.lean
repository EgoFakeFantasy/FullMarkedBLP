import FullMarkedBLP.FrozenSourceBounds

namespace FullMarkedBLP

theorem completion_in_prefix_preserves_later_marks {initial a b : Pattern} {rec : Records} {r y z : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ i row, rowAt b i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r)
    (earlier : ∀ i, i < r → rowAt b i = rowAt a i) {row : Row}
    (hr : rowAt b r = some row) (hm : y ∈ row.marks) (hz : z ∈ row.marks) (hyz : y ≤ z) :
    ∃ nextRow, rowAt (completeMark b rec r y) r = some nextRow ∧ z ∈ nextRow.marks := by
  cases hc : completionRecord b rec r y with
  | none => exact ⟨row, by simp [completeMark, hr, hc], hz⟩
  | some sources =>
    obtain ⟨k, s, xs, _, _, _, _, hb⟩ := completion_sources_between_in_prefix historyValid valid reach earlier hr hm hc
    refine ⟨completeMarkRow row y sources, ?_, ?_⟩
    · simpa only [completeMark, hr, hc] using (rowAt_set_self (new := completeMarkRow row y sources) hr)
    · exact completeMarkRow_preserves_later_marks hz hyz (fun x hx => (hb x hx).2)

theorem list_snoc_induction {α : Type} {P : List α → Prop}
    (nil : P []) (step : ∀ xs x, P xs → P (xs ++ [x])) (xs : List α) : P xs := by
  have h : ∀ ys : List α, P ys.reverse := by
    intro ys
    induction ys with
    | nil => exact nil
    | cons x ys ih => simpa using step ys.reverse x ih
  simpa using h xs.reverse
/-- Pending frozen marks are still present after each processed prefix. -/
theorem frozen_pending_marks {initial a : Pattern} {rec : Records} {r : Nat} {row : Row}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) (hr : rowAt a r = some row)
    (sorted : row.marks.Pairwise (· < ·))
    (prefixValid : ∀ processed, processed <+: row.marks →
      ∀ i currentRow, rowAt (processed.foldl (fun current y => completeMark current rec r y) a) i = some currentRow → currentRow.CoreValid i)
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
    have hpre : processed <+: row.marks := ⟨y :: pending, hsplit'⟩
    obtain ⟨nextRow, hn, hzn⟩ := completion_in_prefix_preserves_later_marks historyValid
      (prefixValid processed hpre) reach
      (fun i hi => completeMarks_fold_other_row processed (by omega : i ≠ r)) hc hym hzm (by omega)
    exact ⟨nextRow, by simpa [List.foldl_append] using hn, hzn⟩

end FullMarkedBLP


