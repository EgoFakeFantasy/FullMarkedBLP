import FullMarkedBLP.ScanTermination

namespace FullMarkedBLP

theorem rowAt_exists {a : Pattern} {r : Nat} (hr : 0 < r) (hb : r ≤ a.length) :
    ∃ row, rowAt a r = some row := by
  have hi : r - 1 < a.length := by omega
  refine ⟨a[r - 1], ?_⟩
  simp [rowAt, Nat.ne_of_gt hr, hi]

theorem fromRight_exists {xs : List Nat} {k : Nat} (hk : 0 < k) (hb : k ≤ xs.length) :
    ∃ v, fromRight xs k = some v := by
  have hi : xs.length - k < xs.length := by omega
  refine ⟨xs[xs.length - k], ?_⟩
  simp [fromRight, hk, hb, hi]

theorem Row.step_lt_length {row : Row} (h : row.OrdinaryShape) :
    row.step < row.core.length := by
  rcases h with ⟨hp, h | h | h⟩ <;> omega

theorem Row.b_exists {r : Nat} {row : Row} (h : row.CoreValid r) :
    ∃ b, row.b = some b := fromRight_exists (by decide) h.2.1

theorem nativeSourcesFuel_total {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (p fuel : Nat) : ∀ u, 0 < u → u ≤ a.length → u < fuel →
    ∃ sources, nativeSourcesFuel a p fuel u = some sources := by
  induction fuel with
  | zero => intro u _ _ hf; omega
  | succ fuel ih =>
    intro u hu hb hf
    obtain ⟨row, hr⟩ := rowAt_exists hu hb
    obtain ⟨b, hbb⟩ := Row.b_exists (valid u row hr)
    by_cases hp : p < b
    · have hd := native_source_lt valid hr hbb
      obtain ⟨tail, ht⟩ := ih b (by omega) (by omega) (by omega)
      refine ⟨b :: tail, ?_⟩
      simp [nativeSourcesFuel, hr, hbb, hp, ht]
    · refine ⟨[], ?_⟩
      simp [nativeSourcesFuel, hr, hbb, hp]

theorem fromRight_pos {xs : List Nat} {k v : Nat}
    (hs : xs.Pairwise (· < ·)) (hk : 0 < k) (hb : k < xs.length)
    (hv : fromRight xs k = some v) : 0 < v := by
  have hx : k ≤ xs.length := by omega
  simp only [fromRight, hk, hx, and_self, ↓reduceIte] at hv
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hv
  have hh := List.pairwise_iff_getElem.mp hs 0 (xs.length - k)
    (by omega) hi (by omega)
  rw [he] at hh
  omega

theorem fromRight_le_last {xs : List Nat} {r k v : Nat}
    (hs : xs.Pairwise (· < ·)) (hl : xs.getLast? = some r)
    (hk : 0 < k) (hv : fromRight xs k = some v) : v ≤ r := by
  by_cases he : k = 1
  · subst k
    unfold fromRight at hv
    split at hv
    next =>
      rw [← List.getLast?_eq_getElem?] at hv
      have hh := Option.some.inj (hv.symm.trans hl)
      omega
    next => simp at hv
  · exact Nat.le_of_lt (fromRight_lt_last hs hl (by omega) hv)

theorem nativeSources_total {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} (hr : rowAt a r = some row) :
    ∃ sources, nativeSources a r = some sources := by
  have hv := valid r row hr
  by_cases hlong : 2 * row.step < row.core.length
  · exact ⟨[], by simp [nativeSources, hr, hlong]⟩
  · have hstep := Row.step_lt_length hv.2.2.2
    have hpos := hv.2.2.2.1
    obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1)
      (by omega) (by omega)
    obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hpos (by omega)
    have hepos := fromRight_pos hv.1 hpos hstep he
    have heb := fromRight_le_last hv.1 hv.2.2.1 hpos he
    have hrb := rowAt_bounds hr
    obtain ⟨ss, hh⟩ := nativeSourcesFuel_total valid p (e + 1) e hepos (by omega) (by omega)
    exact ⟨ss, by simp [nativeSources, hr, hlong, Row.p, Row.e, hp, he, hh]⟩

end FullMarkedBLP
