import FullMarkedBLP.AuxiliaryClosure

namespace FullMarkedBLP

theorem option_mapM_exists {α β : Type} {f : α → Option β} {xs : List α}
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun z hz => h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

theorem copiedRow_exists_of_entries {a : Pattern} {last row : Row} {source : Nat}
    (h : ∀ x ∈ row.full source, ∃ y, copyEntry a.length last x = some y) :
    ∃ copied, copiedRow a last source row = some copied := by
  obtain ⟨full, hf⟩ := option_mapM_exists h
  have hc : copiedCore a.length last source row = some full.dropLast := by
    simp [copiedCore, hf]
  simp only [copiedRow, hc]
  exact ⟨_, rfl⟩

theorem auxiliaryStep_total {a : Pattern} {anchor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (ha : 0 < anchor) (hab : anchor ≤ a.length) (hlen : 2 ≤ a.length) :
    ∃ b, auxiliaryStep anchor a = some b := by
  let aux : Row := ⟨[anchor, a.length + 1], 1, []⟩
  let extended := a ++ [aux]
  let sources := (List.range (a.length + 1 - anchor)).map (anchor + ·)
  have haux : shortCopySources aux = some sources := by
    simp [shortCopySources, aux, Row.p, Row.e, fromRight, show anchor ≠ 0 by omega, sources]
  have hmap : ∀ source ∈ sources, ∃ copied, (do
      let row ← rowAt extended source
      copiedRow extended aux source row) = some copied := by
    intro source hs
    obtain ⟨i, hi, hiEq⟩ := List.mem_map.mp hs
    have hir : i < a.length + 1 - anchor := List.mem_range.mp hi
    have hsource : 0 < source ∧ source ≤ a.length := by omega
    obtain ⟨row, hr⟩ := rowAt_exists (a := a) hsource.1 hsource.2
    have hre : rowAt extended source = some row := (prefix_rowAt (List.prefix_append a [aux]) hsource.2).trans hr
    have hv := valid source row hr
    have hentries : ∀ x ∈ row.full source, ∃ y, copyEntry extended.length aux x = some y := by
      intro x hx
      have hbound : x ≤ a.length + 1 := by
        simp only [Row.full, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · have hh := core_entry_le_owner hv hx; omega
        · omega
      exact ⟨_, by simpa [extended, aux] using auxiliary_copy_entry anchor (a.length + 1) x ha hbound⟩
    obtain ⟨copied, hc⟩ := copiedRow_exists_of_entries hentries
    exact ⟨copied, by simp [hre, hc]⟩
  obtain ⟨copied, hc⟩ := option_mapM_exists hmap
  refine ⟨extended.dropLast ++ copied, ?_⟩
  change shortCopy extended = _
  have hlast : extended.getLast? = some aux := by simp [extended]
  have hsize : ¬extended.length ≤ 2 := by simp [extended]; omega
  unfold shortCopy
  rw [if_neg hsize, hlast]
  dsimp only [Bind.bind, Option.bind]
  rw [haux]
  dsimp only [Bind.bind, Option.bind]
  dsimp only [Bind.bind, Option.bind] at hc
  rw [hc]
  rfl

theorem expandFrom_total_coreValid {a : Pattern} {anchor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (ha : 0 < anchor) (hab : anchor ≤ a.length) (hlen : 2 ≤ a.length) (k : Nat) :
    ∃ b, expandFrom anchor a k = some b ∧
      (∀ r row, rowAt b r = some row → row.CoreValid r) := by
  induction k with
  | zero => exact ⟨a, rfl, valid⟩
  | succ k ih =>
    obtain ⟨previous, hp, hv⟩ := ih
    have hlength := (expandFrom_prefix hp).length_le
    have hab' : anchor ≤ previous.length := by omega
    obtain ⟨b, hb⟩ := auxiliaryStep_total hv ha hab' (by omega)
    exact ⟨b, by simp [expandFrom, hp, hb], auxiliaryStep_preserves_coreValid hv hab' hb⟩

theorem expandFrom_preserves_marks_traces {a b : Pattern} {anchor k : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (traces : ∀ r row, rowAt a r = some row → row.HasTraces a)
    (ha : anchor ≤ a.length) (h : expandFrom anchor a k = some b) :
    (∀ r row, rowAt b r = some row → row.CoreValid r) ∧
    (∀ r row, rowAt b r = some row → row.ProperMarks r) ∧
    (∀ r row, rowAt b r = some row → row.HasTraces b) := by
  induction k generalizing b with
  | zero =>
    have he : a = b := Option.some.inj h
    subst b
    exact ⟨valid, marks, traces⟩
  | succ k ih =>
    obtain ⟨previous, hp, hb⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hv, hm, ht⟩ := ih hp
    have hlength := (expandFrom_prefix hp).length_le
    have hab : anchor ≤ previous.length := by omega
    exact ⟨auxiliaryStep_preserves_coreValid hv hab hb,
      auxiliaryStep_preserves_properMarks hv hm hab hb,
      auxiliaryStep_preserves_traces hv hm ht hab hb⟩

end FullMarkedBLP




