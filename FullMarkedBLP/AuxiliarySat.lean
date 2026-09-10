import FullMarkedBLP.ExpansionTotal

namespace FullMarkedBLP

theorem auxiliary_append_sat {a : Pattern} {anchor : Nat} (hs : Sat a) :
    Sat (a ++ [⟨[anchor, a.length + 1], 1, []⟩]) := by
  intro r row hr hel
  let aux : Row := ⟨[anchor, a.length + 1], 1, []⟩
  have hpre : a <+: a ++ [aux] := List.prefix_append _ _
  by_cases hbefore : r ≤ a.length
  · have ha : rowAt a r = some row := (prefix_rowAt hpre hbefore).symm.trans hr
    obtain ⟨p, e, er, v, hp, he, her, hb, hv⟩ := hs r row ha hel
    exact ⟨p, e, er, v, hp, he, (prefix_rowAt hpre (rowAt_bounds her).2).trans her, hb, hv⟩
  · have hbounds := rowAt_bounds hr
    have heq : r = a.length + 1 := by simp only [List.length_append, List.length_singleton] at hbounds; omega
    subst r
    have hrow : row = aux := by
      simpa [rowAt, aux, List.getElem?_append_right (Nat.le_refl a.length)] using hr.symm
    subst row
    refine ⟨anchor, a.length + 1, aux, anchor, ?_, ?_, hr, ?_, Nat.le_refl _⟩ <;>
      simp [aux, Row.p, Row.e, Row.b, fromRight]

theorem shortCopy_sat_low_endpoint {a b : Pattern} {last row copied : Row}
    {r minimum : Nat}
    (valid : ∀ i rw, rowAt a i = some rw → rw.CoreValid i)
    (hs : Sat a) (h : shortCopy a = some b)
    (hm : last.core.head? = some minimum) (hmin : minimum ≤ a.dropLast.length)
    (hr : rowAt a r = some row) (hc : copiedRow a last r row = some copied)
    (hel : row.core.length ≤ 2 * row.step)
    (hlow : ∀ e, row.e = some e → e < minimum) :
    ∃ p e er v, copied.p = some p ∧ copied.e = some e ∧
      rowAt b e = some er ∧ er.b = some v ∧ v ≤ p := by
  obtain ⟨p, e, er, v, hp, he, her, hb, hv⟩ := hs r row hr hel
  have helo := hlow e he
  have hpe := row_p_lt_e (valid r row hr) hp he
  obtain ⟨p', hpp, hpm⟩ := copiedRow_p hp hc
  obtain ⟨e', hee, hem⟩ := copiedRow_e he hc
  have hpeq := copyEntry_low_value hm (by omega : p < minimum) hpm
  have heeq := copyEntry_low_value hm helo hem
  subst p'
  subst e'
  have hbound : e ≤ a.dropLast.length := by omega
  have hprefix := shortCopy_prefix h
  have herpre : rowAt a.dropLast e = some er :=
    (prefix_rowAt (List.dropLast_prefix a) hbound).symm.trans her
  exact ⟨p, e, er, v, hpp, hee, (prefix_rowAt hprefix hbound).trans herpre, hb, hv⟩

theorem auxiliary_copied_row_sat {a b : Pattern} {anchor source : Nat} {row copied : Row}
    (valid : ∀ i rw, rowAt a i = some rw → rw.CoreValid i)
    (hs : Sat a) (ha : anchor ≤ a.length)
    (h : auxiliaryStep anchor a = some b)
    (hr : rowAt a source = some row)
    (hc : copiedRow (a ++ [⟨[anchor, a.length + 1], 1, []⟩])
      ⟨[anchor, a.length + 1], 1, []⟩ source row = some copied)
    (hel : row.core.length ≤ 2 * row.step) :
    ∃ p e er v, copied.p = some p ∧ copied.e = some e ∧
      rowAt b e = some er ∧ er.b = some v ∧ v ≤ p := by
  let aux : Row := ⟨[anchor, a.length + 1], 1, []⟩
  let extended := a ++ [aux]
  have hv := auxiliary_append_coreValid valid ha
  have hsat := auxiliary_append_sat (anchor := anchor) hs
  have hre : rowAt extended source = some row :=
    (prefix_rowAt (List.prefix_append a [aux]) (rowAt_bounds hr).2).trans hr
  obtain ⟨p, e, er, v, hp, he, her, hb, hle⟩ := hs source row hr hel
  by_cases hlo : e < anchor
  · apply shortCopy_sat_low_endpoint hv hsat h (by rfl : aux.core.head? = some anchor)
      (by simpa [aux] using ha) hre hc hel
    intro e' he'
    have heq := Option.some.inj (he'.symm.trans he)
    omega
  · apply shortCopy_sat_copied_endpoint (threshold := anchor) (upper := a.length + 1) hsat h (by simp)
      (by simp [Row.p, fromRight]) (by simp [Row.e, fromRight])
      (by simpa [extended] using auxiliary_row_coreValid ha)
      (by simp; omega) hre hc hel
    intro e' he'
    have heq := Option.some.inj (he'.symm.trans he)
    have heb := (rowAt_bounds her).2
    constructor <;> omega

end FullMarkedBLP


