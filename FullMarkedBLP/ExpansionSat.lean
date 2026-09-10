import FullMarkedBLP.AuxiliarySat

namespace FullMarkedBLP

theorem auxiliaryStep_preserves_sat {a b : Pattern} {anchor : Nat}
    (valid : ∀ i rw, rowAt a i = some rw → rw.CoreValid i)
    (hs : Sat a) (ha : anchor ≤ a.length)
    (h : auxiliaryStep anchor a = some b) : Sat b := by
  intro r row hr hel
  have hpre := auxiliaryStep_prefix h
  by_cases hbefore : r ≤ a.length
  · have hold : rowAt a r = some row := (prefix_rowAt hpre hbefore).symm.trans hr
    obtain ⟨p, e, er, v, hp, he, her, hb, hv⟩ := hs r row hold hel
    exact ⟨p, e, er, v, hp, he, (prefix_rowAt hpre (rowAt_bounds her).2).trans her, hb, hv⟩
  · let aux : Row := ⟨[anchor, a.length + 1], 1, []⟩
    let extended := a ++ [aux]
    have hc := h
    change shortCopy extended = some b at hc
    unfold shortCopy at hc
    split at hc
    next => simp at hc
    next =>
      obtain ⟨last, hl, hc⟩ := Option.bind_eq_some_iff.mp hc
      have heq : last = aux := by simpa [extended] using hl.symm
      subst last
      obtain ⟨sources, hsrc, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨copied, hmap, hout⟩ := Option.bind_eq_some_iff.mp hc
      have hbout : a ++ copied = b := by simpa [extended] using Option.some.inj hout
      have hr' : rowAt (a ++ copied) r = some row := by simpa [hbout] using hr
      have hget : copied[r - 1 - a.length]? = some row := by
        simpa [rowAt, show r ≠ 0 by omega, List.getElem?_append_right (show a.length ≤ r - 1 by omega)] using hr'
      obtain ⟨source, hsource, hrow⟩ := (option_mapM_forall2 hmap).mem_right (List.mem_of_getElem? hget)
      obtain ⟨old, hold, hcopy⟩ := Option.bind_eq_some_iff.mp hrow
      obtain ⟨p, e, hp, he, _, hsources⟩ := shortCopySources_description hsrc
      have hpval : p = anchor := by simpa [aux, Row.p, fromRight] using hp.symm
      have heval : e = a.length + 1 := by simpa [aux, Row.e, fromRight] using he.symm
      rw [hsources] at hsource
      obtain ⟨i, hi, hiEq⟩ := List.mem_map.mp hsource
      have hir := List.mem_range.mp hi
      have hbound : source ≤ a.length := by omega
      have holda : rowAt a source = some old :=
        (prefix_rowAt (List.prefix_append a [aux]) hbound).symm.trans hold
      have helold : old.core.length ≤ 2 * old.step := by
        obtain ⟨core, hcore, heq⟩ := Option.bind_eq_some_iff.mp hcopy
        cases Option.some.inj heq
        simpa only [copiedCore_length hcore] using hel
      exact auxiliary_copied_row_sat valid hs ha h holda hcopy helold

theorem expandFrom_preserves_sat {a b : Pattern} {anchor k : Nat}
    (valid : ∀ i rw, rowAt a i = some rw → rw.CoreValid i)
    (hs : Sat a) (ha : anchor ≤ a.length)
    (h : expandFrom anchor a k = some b) :
    (∀ i rw, rowAt b i = some rw → rw.CoreValid i) ∧ Sat b := by
  induction k generalizing b with
  | zero =>
    have he : a = b := Option.some.inj h
    subst b
    exact ⟨valid, hs⟩
  | succ k ih =>
    obtain ⟨previous, hp, hb⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hv, hsat⟩ := ih hp
    have hlength := (expandFrom_prefix hp).length_le
    have hab : anchor ≤ previous.length := by omega
    exact ⟨auxiliaryStep_preserves_coreValid hv hab hb,
      auxiliaryStep_preserves_sat hv hsat hab hb⟩

theorem expand_preserves_sat {a b : Pattern} {k : Nat}
    (valid : ∀ i rw, rowAt a i = some rw → rw.CoreValid i)
    (hs : Sat a) (h : expand a k = some b) : Sat b := by
  unfold expand at h
  split at h
  next kind =>
    obtain ⟨row, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨anchor, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨initial, hc, he⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨last, hlast, hm⟩ := classify_expand_last kind
    have heq : last = row := Option.some.inj (hlast.symm.trans hl)
    subst last
    have hli := hl
    rw [List.getLast?_eq_getElem?] at hli
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hli
    have hr : rowAt a a.length = some row := by
      simpa [rowAt, show a.length ≠ 0 by omega] using hli
    obtain ⟨anch, hanch, _, hab, hsize⟩ := coreValid_expansion_bounds (valid _ _ hr) hm
    have hae : anch = anchor := Option.some.inj (hanch.symm.trans hb)
    subst anch
    have hic : initial = a.dropLast := by simpa [cut, hsize] using hc.symm
    have hbound : anchor ≤ initial.length := by simp [hic]; exact hab
    exact (expandFrom_preserves_sat (cut_preserves_coreValid valid hc)
      (cut_preserves_sat valid hs hc) hbound he).2
  next => simp at h

theorem expand_total_invariants {a : Pattern}
    (valid : ∀ i rw, rowAt a i = some rw → rw.CoreValid i)
    (marks : ∀ i rw, rowAt a i = some rw → rw.ProperMarks i)
    (traces : ∀ i rw, rowAt a i = some rw → rw.HasTraces a)
    (hs : Sat a) (kind : classify a = .successor ∨ classify a = .limit) (k : Nat) :
    ∃ b, expand a k = some b ∧
      (∀ i rw, rowAt b i = some rw → rw.CoreValid i) ∧
      (∀ i rw, rowAt b i = some rw → rw.ProperMarks i) ∧
      (∀ i rw, rowAt b i = some rw → rw.HasTraces b) ∧ Sat b := by
  obtain ⟨b, hb, hv⟩ := expand_total_coreValid valid kind k
  obtain ⟨_, hm, ht⟩ := expand_preserves_marks_traces valid marks traces hb
  exact ⟨b, hb, hv, hm, ht, expand_preserves_sat valid hs hb⟩

end FullMarkedBLP


