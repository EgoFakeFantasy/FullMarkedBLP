import FullMarkedBLP.CopyShortKey
import FullMarkedBLP.PrefixChildren

namespace FullMarkedBLP

theorem classify_expand_last_two_high {a : Pattern} {last : Row}
    (kind : classify a = .successor ∨ classify a = .limit)
    (hl : a.getLast? = some last) (valid : last.CoreValid a.length) :
    last.core.length = last.step + 2 := by
  unfold classify at kind
  split at kind
  next => simp at kind
  next =>
    simp only [hl] at kind
    split at kind
    next successor =>
      have len : last.core.length = 4 := successor.2
      have shape := valid.2.2.2
      rcases shape with ⟨_, h | h | h⟩ <;> omega
    next =>
      split at kind
      next limit => omega
      next => simp at kind

theorem auxiliaryStep_first_shortKey_lt {a b : Pattern} {anchor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (bound : anchor ≤ a.length) (run : auxiliaryStep anchor a = some b)
    (tail : List Nat) :
    ∃ copied, rowAt b (a.length + 1) = some copied ∧
      copied.shortKey < (a.length + 1) :: anchor :: tail := by
  let aux : Row := ⟨[anchor, a.length + 1], 1, []⟩
  let extended := a ++ [aux]
  have hp : aux.p = some anchor := by simp [aux, Row.p, fromRight]
  have he : aux.e = some (a.length + 1) := by simp [aux, Row.e, fromRight]
  obtain ⟨row, copied, sourceAt, copy, copiedAt⟩ := shortCopy_copied_rowAt run
    (by simp [aux]) hp he (Nat.le_refl _) (by omega)
    (by simp only [List.length_append, List.length_singleton]; omega)
  have validExtended := auxiliary_append_coreValid valid bound
  have validAux : aux.CoreValid extended.length := by
    simpa [extended] using auxiliary_row_coreValid bound
  have validSource := validExtended anchor row sourceAt
  have copiedValid := copiedRow_coreValid_shift validAux validSource hp (Nat.le_refl _) copy
  have ownerEq : anchor + (extended.length - anchor) = a.length + 1 := by
    simp only [extended, List.length_append, List.length_singleton]
    omega
  rw [ownerEq] at copiedValid copiedAt
  obtain ⟨rest, keyEq⟩ := List.head?_eq_some_iff.mp (Row.shortKey_head copiedValid)
  refine ⟨copied, copiedAt, ?_⟩
  rw [keyEq]
  apply List.Lex.cons
  cases rest with
  | nil => exact List.Lex.nil
  | cons x xs =>
    have member : x ∈ copied.shortKey := by simp [keyEq]
    have allowed := copied_first_core_allowed validAux validSource hp
      (by rfl : aux.core.head? = some anchor) copy x (Row.shortKey_mem_core member)
    have smaller : x < a.length + 1 := by
      have decreasing := Row.shortKey_decreasing copiedValid.1 copiedValid.2.2.2.1
      rw [keyEq] at decreasing
      exact (List.pairwise_cons.mp decreasing).1 x (by simp)
    apply List.Lex.rel
    rcases allowed with low | high
    · exact low
    · have eq : x = a.length + 1 := by simpa [aux] using high
      omega

/-- Every positive fixed-anchor expansion strictly decreases the literal
short key. The first auxiliary row is preserved by every later parameter. -/
theorem expand_shortKey_lt {a b : Pattern} {k : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (positive : 0 < k) (run : expand a k = some b) : shortKey b < shortKey a := by
  have initialPrefix := expand_cut_prefix run
  unfold expand at run
  split at run
  next kind =>
    obtain ⟨last, lastAt, rest⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨anchor, anchorAt, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨initial, cutEq, expansion⟩ := Option.bind_eq_some_iff.mp rest
    have cutCopy := cutEq
    unfold cut at cutCopy
    split at cutCopy
    next size =>
      cases Option.some.inj cutCopy
      have rowAtLast : rowAt a a.length = some last := by
        simpa [rowAt, show a.length ≠ 0 by omega, List.getLast?_eq_getElem?] using lastAt
      have validLast := valid _ _ rowAtLast
      have twoHigh := classify_expand_last_two_high kind lastAt validLast
      obtain ⟨classified, classifiedAt, len⟩ := classify_expand_last kind
      have eq := Option.some.inj (classifiedAt.symm.trans lastAt)
      subst classified
      obtain ⟨anch, anchAt, anchorPositive, anchorBound, _⟩ :=
        coreValid_expansion_bounds validLast len
      have eq := Option.some.inj (anchAt.symm.trans anchorAt)
      subst anch
      have cutValid := cut_preserves_coreValid valid cutEq
      obtain ⟨first, firstRun⟩ := auxiliaryStep_total cutValid anchorPositive
        (by simpa using anchorBound) (by simp; omega)
      have one : expandFrom anchor a.dropLast 1 = some first := by
        simpa [expandFrom] using firstRun
      have nested := expandFrom_nested (by omega : 1 ≤ k) one expansion
      obtain ⟨copied, copiedAt, smaller⟩ := auxiliaryStep_first_shortKey_lt cutValid
        (by simpa using anchorBound) firstRun (last.core.take 1)
      have length : a.dropLast.length + 1 = a.length := by simp; omega
      rw [length] at copiedAt smaller
      have copiedAtFinal := (prefix_rowAt nested (rowAt_bounds copiedAt).2).trans copiedAt
      apply shortKey_lt_of_cut_prefix lastAt initialPrefix copiedAtFinal
      simpa only [Row.shortKey_two_high validLast twoHigh anchorAt] using smaller
    next => simp at cutCopy
  next => simp at run

end FullMarkedBLP
