import FullMarkedBLP.RankI2Root
import FullMarkedBLP.ScanSatPrefix

namespace FullMarkedBLP

theorem prefix_of_rowAt_agreement {a b : Pattern}
    (same : ∀ i, 0 < i → i ≤ a.length → rowAt b i = rowAt a i) : a <+: b := by
  apply List.prefix_iff_getElem?.mpr
  intro i hi
  have rows := same (i + 1) (by omega) (by omega)
  simpa only [rowAt, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Nat.add_sub_cancel, List.getElem?_eq_getElem hi] using rows

theorem mStar_cut_prefix {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r) (sat : Sat a)
    (step : mStar a = some b) : a.dropLast <+: b := by
  unfold mStar at step
  split at step
  next transient =>
    obtain ⟨copied, copy, scan⟩ := Option.bind_eq_some_iff.mp step
    obtain ⟨rec, cursor, reach, _, _⟩ := fullScan_reaches_end scan
    apply prefix_of_rowAt_agreement
    intro i positive bound
    have smaller : i < a.length := by simp only [List.length_dropLast] at bound; omega
    exact (shortCopy_scan_old_prefix_rowAt valid sat copy reach smaller).trans
      (prefix_rowAt (List.dropLast_prefix a) bound)
  next => simp at step

theorem expand_cut_prefix {a b : Pattern} {k : Nat} (step : expand a k = some b) : a.dropLast <+: b := by
  unfold expand at step
  split at step
  next kind =>
    obtain ⟨last, _, rest⟩ := Option.bind_eq_some_iff.mp step
    obtain ⟨anchor, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨initial, cutEq, expansion⟩ := Option.bind_eq_some_iff.mp rest
    unfold cut at cutEq
    split at cutEq
    next =>
      have same := Option.some.inj cutEq
      subst initial
      exact expandFrom_prefix expansion
    next => simp at cutEq
  next => simp at step

theorem expandFrom_nested {anchor : Nat} {initial a b : Pattern} {k l : Nat}
    (order : k ≤ l) (first : expandFrom anchor initial k = some a)
    (second : expandFrom anchor initial l = some b) : a <+: b := by
  induction l generalizing b with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    have same := Option.some.inj (first.symm.trans second)
    subst b
    exact List.prefix_refl _
  | succ l ih =>
    by_cases same : k = l + 1
    · subst k
      have equal := Option.some.inj (first.symm.trans second)
      subst b
      exact List.prefix_refl _
    · obtain ⟨previous, hp, hb⟩ := Option.bind_eq_some_iff.mp second
      exact (ih (by omega) hp).trans (auxiliaryStep_prefix hb)

theorem expand_nested {a b c : Pattern} {k l : Nat} (order : k ≤ l)
    (first : expand a k = some b) (second : expand a l = some c) : b <+: c := by
  unfold expand at first second
  split at first
  next kind =>
    rw [if_pos kind] at second
    obtain ⟨last, lastEq, rest⟩ := Option.bind_eq_some_iff.mp first
    rw [lastEq] at second
    change last.b.bind (fun anchor => (cut a).bind (fun initial => expandFrom anchor initial l)) = some c at second
    obtain ⟨anchor, anchorEq, rest⟩ := Option.bind_eq_some_iff.mp rest
    rw [anchorEq, Option.bind_some] at second
    obtain ⟨initial, cutEq, expansion⟩ := Option.bind_eq_some_iff.mp rest
    rw [cutEq, Option.bind_some] at second
    exact expandFrom_nested order expansion second
  next => simp at first

theorem step_cut_prefix {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r) (sat : Sat a)
    (step : Step a b) : a.dropLast <+: b := by
  cases step with
  | cut h =>
    unfold cut at h
    split at h
    next => cases Option.some.inj h; exact List.prefix_refl _
    next => simp at h
  | expand _ h => exact expand_cut_prefix h
  | marked h => exact mStar_cut_prefix valid sat h

theorem expand_not_mStar {a b c : Pattern} {k : Nat}
    (expansion : expand a k = some b) (marked : mStar a = some c) : False := by
  unfold expand at expansion
  split at expansion
  next kind =>
    unfold mStar at marked
    split at marked
    next transient => rw [transient] at kind; cases kind <;> contradiction
    next => simp at marked
  next => simp at expansion

/-- Every actual pair of children of a realized Sat parent is comparable
by literal marked-pattern prefix, before passing to comparison keys. -/
theorem step_children_prefix_comparable {a b c : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r) (sat : Sat a)
    (first : Step a b) (second : Step a c) : b <+: c ∨ c <+: b := by
  cases first with
  | cut h =>
    unfold cut at h
    split at h
    next => cases Option.some.inj h; exact Or.inl (step_cut_prefix valid sat second)
    next => simp at h
  | expand _ h =>
    cases second with
    | cut hc =>
      unfold cut at hc
      split at hc
      next => cases Option.some.inj hc; exact Or.inr (expand_cut_prefix h)
      next => simp at hc
    | expand _ he =>
      rcases le_total (α := Nat) _ _ with order | order
      · exact Or.inl (expand_nested order h he)
      · exact Or.inr (expand_nested order he h)
    | marked hm => exact False.elim (expand_not_mStar h hm)
  | marked h =>
    cases second with
    | cut hc =>
      unfold cut at hc
      split at hc
      next => cases Option.some.inj hc; exact Or.inr (mStar_cut_prefix valid sat h)
      next => simp at hc
    | expand _ he => exact False.elim (expand_not_mStar he h)
    | marked hm =>
      have same := Option.some.inj (h.symm.trans hm)
      subst c
      exact Or.inl (List.prefix_refl _)

end FullMarkedBLP
