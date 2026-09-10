import FullMarkedBLP.ScanFrozenDirectStep

namespace FullMarkedBLP

/-- Appending a verified event extends exactly the prior-prefix evidence. -/
theorem prefix_events_snoc {P : List Nat → Nat → Prop} {processed : List Nat} {y : Nat}
    (old : ∀ done mark suffix, processed = done ++ mark :: suffix → P done mark)
    (current : P processed y) :
    ∀ done mark suffix, processed ++ [y] = done ++ mark :: suffix → P done mark := by
  induction processed generalizing P with
  | nil =>
    intro done mark suffix he
    cases done with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨eq, _⟩ := he
      subst mark
      exact current
    | cons d rest =>
      have length := congrArg List.length he
      simp only [List.length_append, List.length_cons, List.length_nil] at length
      omega
  | cons head tail ih =>
    intro done mark suffix he
    cases done with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨eq, _⟩ := he
      subst mark
      exact old [] head tail rfl
    | cons d rest =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨eq, he⟩ := he
      subst d
      exact ih (P := fun done mark => P (head :: done) mark)
        (fun done mark suffix hh => old (head :: done) mark suffix (by simp only [List.cons_append, hh]))
        current rest mark suffix he

/-- Build prefix states and event evidence together, requiring only previously
proved events at each step rather than evidence for the whole fold. -/
theorem frozen_prefix_bootstrap {P : List Nat → Nat → Prop} {Q : List Nat → Prop}
    (frozen : List Nat) (start : Q [])
    (step : ∀ done y suffix, frozen = done ++ y :: suffix → Q done →
      (∀ previous mark rest, done = previous ++ mark :: rest → P previous mark) →
      P done y ∧ Q (done ++ [y])) :
    Q frozen ∧ ∀ done y suffix, frozen = done ++ y :: suffix → P done y := by
  have go : ∀ remaining done, frozen = done ++ remaining → Q done →
      (∀ previous mark rest, done = previous ++ mark :: rest → P previous mark) →
      Q frozen ∧ ∀ previous mark rest, frozen = previous ++ mark :: rest → P previous mark := by
    intro remaining
    induction remaining with
    | nil =>
      intro done he state events
      simp only [List.append_nil] at he
      subst done
      exact ⟨state, events⟩
    | cons y rest ih =>
      intro done he state events
      obtain ⟨current, next⟩ := step done y rest he state events
      apply ih (done ++ [y]) (by simpa only [List.append_assoc, List.singleton_append] using he) next
      exact prefix_events_snoc events current
  exact go frozen [] rfl start (by intro previous mark rest he; simp at he)

/-- The direct-word frozen fold closes without assuming its intermediate
realizations or event geometry. The direct-word hypothesis remains explicit. -/
theorem scanRankReach_direct_frozen_fold {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (h : RankRowRealization a theta embedding) {row : Row} (hr : rowAt a r = some row)
    (direct : ∀ done y suffix, row.marks = done ++ y :: suffix →
      ∃ source, computeMarkTrace (done.foldl (fun current z => completeMark current rec r z) a) r y = some [y, source]) :
    RankRowRealization (completeFrozenMarks a rec r) theta embedding ∧
    ∀ done y suffix, row.marks = done ++ y :: suffix →
      CompletionEventGeometry (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding := by
  have result := frozen_prefix_bootstrap
    (P := fun done y => CompletionEventGeometry
      (done.foldl (fun current z => completeMark current rec r z) a) rec r y theta embedding)
    (Q := fun done => RankRowRealization
      (done.foldl (fun current z => completeMark current rec r z) a) theta embedding)
    row.marks h (by
      intro done y suffix splitMarks state events
      obtain ⟨source, computed⟩ := direct done y suffix splitMarks
      have rb := rowAt_bounds hr
      obtain ⟨currentRow, currentAt⟩ := rowAt_exists
        (a := done.foldl (fun current z => completeMark current rec r z) a) rb.1
        (by simpa only [completeMarks_fold_length] using rb.2)
      obtain ⟨event, next⟩ := scanRankReach_frozen_direct_step reach entryRealization geometry
        done suffix events state hr (h.proper r row hr).1 splitMarks currentAt computed
      exact ⟨event, by simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using next⟩)
  exact ⟨by simpa only [completeFrozenMarks, hr] using result.1, result.2⟩

end FullMarkedBLP


