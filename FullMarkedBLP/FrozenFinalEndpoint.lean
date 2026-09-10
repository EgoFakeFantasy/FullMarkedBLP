import FullMarkedBLP.CompletionEndpointUpdate
import FullMarkedBLP.FrozenRecordDecision

namespace FullMarkedBLP

/-- When B is the final original mark, the whole frozen fold reads its entrance record. -/
theorem completeFrozenMarks_b_final_mark {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r v : Nat} (h : RankRowRealization a theta embedding)
    {row out : Row} (hr : rowAt a r = some row) (hb : row.b = some v)
    (processed : List Nat) (splitMarks : row.marks = processed ++ [v])
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (hout : rowAt (completeFrozenMarks a rec r) r = some out) :
    out.b = some (v + ((completionRecord a rec r v).getD []).length) := by
  have earlier : ∀ y ∈ processed, y < v := by
    have sorted := (h.proper r row hr).1
    rw [splitMarks] at sorted
    exact fun y hy => (List.pairwise_append.mp sorted).2.2 y hy v (by simp)
  have prior : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding := by
    intro done mark suffix eq
    apply events done mark (suffix ++ [v])
    simpa only [eq, List.append_assoc, List.cons_append] using splitMarks
  have bounds := rowAt_bounds hr
  obtain ⟨mid, atMid⟩ := rowAt_exists (a := processed.foldl (fun current y => completeMark current rec r y) a)
    bounds.1 (by simpa only [completeMarks_fold_length] using bounds.2)
  have validMid := frozen_fold_coreValid processed h.valid prior r mid atMid
  obtain ⟨w, hw⟩ := fromRight_exists (xs := mid.core) (k := 2) (by decide) validMid.2.1
  have same := frozen_fold_b_eq_of_marks_lt_b processed earlier prior hr atMid
    (h.valid r row hr) validMid hb hw
  have midB : mid.b = some v := by simpa only [same] using hw
  have lastEvent := events processed v [] splitMarks
  have atOut : rowAt (completeMark
      (processed.foldl (fun current y => completeMark current rec r y) a) rec r v) r = some out := by
    simpa only [completeFrozenMarks, hr, splitMarks, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using hout
  have update := completionEvent_b_update lastEvent atMid midB atOut
  have recordEq := realized_frozen_completionRecord_eq h processed prior hr
    (show v ∈ row.marks by rw [splitMarks]; simp)
  simpa only [recordEq, ite_true] using update

end FullMarkedBLP
