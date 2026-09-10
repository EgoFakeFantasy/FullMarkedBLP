import FullMarkedBLP.CopyPredecessor

namespace FullMarkedBLP

/-- Recover the exact source interval and copied block of a successful short copy. -/
theorem shortCopy_decomposition {a b : Pattern} {last : Row} {p e : Nat}
    (copy : shortCopy a = some b) (lastAt : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e) :
    2 < a.length ∧ p ≠ 0 ∧ ∃ block : Pattern,
      ((List.range (e - p)).map (p + ·)).mapM (fun source => do
        let row ← rowAt a source
        copiedRow a last source row) = some block ∧ b = a.dropLast ++ block := by
  unfold shortCopy at copy
  split at copy
  next => simp at copy
  next hn =>
    obtain ⟨last', lastAt', copy⟩ := Option.bind_eq_some_iff.mp copy
    have same := Option.some.inj (lastAt'.symm.trans lastAt)
    subst last'
    obtain ⟨sources, sourcesEq, copy⟩ := Option.bind_eq_some_iff.mp copy
    obtain ⟨block, blockEq, copy⟩ := Option.bind_eq_some_iff.mp copy
    obtain ⟨p', e', hp', he', nonzero, sourceShape⟩ := shortCopySources_description sourcesEq
    have sameP := Option.some.inj (hp'.symm.trans hp)
    have sameE := Option.some.inj (he'.symm.trans he)
    subst p'; subst e'
    exact ⟨by omega, nonzero, block, sourceShape ▸ blockEq, (Option.some.inj copy).symm⟩

theorem shortCopy_length {a b : Pattern} {last : Row} {p e : Nat}
    (copy : shortCopy a = some b) (lastAt : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e) :
    b.length = a.length - 1 + (e - p) := by
  obtain ⟨_, _, block, blockEq, result⟩ := shortCopy_decomposition copy lastAt hp he
  have blockLength := option_mapM_length blockEq
  simp only [result, List.length_append, List.length_dropLast, blockLength,
    List.length_map, List.length_range]

/-- Every row beyond the retained prefix comes from its literal source;
there are no additional rows hidden by the partial computation. -/
theorem shortCopy_row_origin {a b : Pattern} {last copied : Row} {p e target : Nat}
    (copy : shortCopy a = some b) (lastAt : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e) (hpn : p ≤ a.length)
    (afterPrefix : a.length ≤ target) (targetAt : rowAt b target = some copied) :
    ∃ source row, p ≤ source ∧ source < e ∧ target = source + (a.length - p) ∧
      rowAt a source = some row ∧ copiedRow a last source row = some copied := by
  obtain ⟨hn, _, block, blockEq, result⟩ := shortCopy_decomposition copy lastAt hp he
  have index : target - 1 - a.dropLast.length = target - a.length := by simp; omega
  have atBlock : block[target - a.length]? = some copied := by
    rw [result] at targetAt
    simpa only [rowAt, if_neg (by omega : target ≠ 0),
      List.getElem?_append_right (by simp; omega : a.dropLast.length ≤ target - 1), index] using targetAt
  obtain ⟨source, sourceAt, rowCopy⟩ := (option_mapM_forall2 blockEq).at atBlock
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp sourceAt
  have bound' : target - a.length < e - p := by simpa using bound
  have value' : p + (target - a.length) = source := by simpa using value
  obtain ⟨row, rowAtSource, copiedEq⟩ := Option.bind_eq_some_iff.mp rowCopy
  exact ⟨source, row, by omega, by omega, by omega, rowAtSource, copiedEq⟩

end FullMarkedBLP
