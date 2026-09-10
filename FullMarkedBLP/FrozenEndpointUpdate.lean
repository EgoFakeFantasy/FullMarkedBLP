import FullMarkedBLP.FrozenFinalEndpoint

namespace FullMarkedBLP

/-- A proper mark at B must be the final mark. -/
theorem properMarks_b_last {row : Row} {r v : Nat}
    (hv : row.CoreValid r) (hm : row.ProperMarks r) (hb : row.b = some v)
    (mem : v ∈ row.marks) : ∃ processed, row.marks = processed ++ [v] := by
  obtain ⟨processed, suffix, eq⟩ := List.append_of_mem mem
  have sorted := hm.1
  rw [eq] at sorted
  have tailEmpty : suffix = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    have lt : v < z := (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 z hz
    have zm : z ∈ row.marks := by rw [eq]; simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hz)
    obtain ⟨zr, k, _, zk⟩ := hm.2 z zm
    have le := core_entry_le_b hv hb (List.mem_of_getElem? zk) zr
    omega
  exact ⟨processed, by simpa only [tailEmpty] using eq⟩

/-- Exact B after the entire frozen completion, using only entrance data. -/
theorem completeFrozenMarks_b_update {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r v : Nat} (h : RankRowRealization a theta embedding)
    {row out : Row} (hr : rowAt a r = some row) (hb : row.b = some v)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (hout : rowAt (completeFrozenMarks a rec r) r = some out) :
    out.b = some (v + if v ∈ row.marks then
      ((completionRecord a rec r v).getD []).length else 0) := by
  by_cases mem : v ∈ row.marks
  · obtain ⟨processed, splitMarks⟩ := properMarks_b_last (h.valid r row hr) (h.proper r row hr) hb mem
    simpa only [mem, ite_true] using
      completeFrozenMarks_b_final_mark h hr hb processed splitMarks events hout
  · have earlier : ∀ y ∈ row.marks, y < v := by
      intro y hy
      obtain ⟨yr, k, _, yk⟩ := (h.proper r row hr).2 y hy
      have le := core_entry_le_b (h.valid r row hr) hb (List.mem_of_getElem? yk) yr
      have ne : y ≠ v := by intro eq; subst y; exact mem hy
      omega
    have atOut : rowAt (row.marks.foldl (fun current y => completeMark current rec r y) a) r = some out := by
      simpa only [completeFrozenMarks, hr] using hout
    have ho := frozen_fold_coreValid row.marks h.valid events r out atOut
    obtain ⟨w, hw⟩ := fromRight_exists (xs := out.core) (k := 2) (by decide) ho.2.1
    have eq := frozen_fold_b_eq_of_marks_lt_b row.marks earlier events hr atOut
      (h.valid r row hr) ho hb hw
    simpa only [mem, ite_false, Nat.add_zero, eq] using hw

end FullMarkedBLP

