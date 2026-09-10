import FullMarkedBLP.Shift

namespace FullMarkedBLP

theorem blockCoreValid_append {base : Nat} {a b : Pattern}
    (ha : BlockCoreValid base a) (hb : BlockCoreValid (base + a.length) b) :
    BlockCoreValid base (a ++ b) := by
  intro i hi
  by_cases he : i < a.length
  · simpa only [List.getElem_append_left he] using ha i he
  · have hj : i - a.length < b.length := by simp only [List.length_append] at hi; omega
    have hh := hb (i - a.length) hj
    have hidx : base + a.length + (i - a.length) = base + i := by omega
    simpa [List.getElem_append_right (by omega : a.length ≤ i), hidx] using hh

theorem blockCoreValid_take {base : Nat} {a : Pattern} (h : BlockCoreValid base a) (n : Nat) :
    BlockCoreValid base (a.take n) := by
  intro i hi
  have hh : i < a.length := by simp only [List.length_take] at hi; omega
  simpa using h i hh

theorem blockCoreValid_drop {base : Nat} {a : Pattern} (h : BlockCoreValid base a) (n : Nat) :
    BlockCoreValid (base + n) (a.drop n) := by
  intro i hi
  have hh : n + i < a.length := by simp only [List.length_drop] at hi; omega
  simpa [Nat.add_assoc] using h (n + i) hh

theorem blockCoreValid_shift {base r t : Nat} {a : Pattern}
    (h : BlockCoreValid base a) (hr : r < base) :
    BlockCoreValid (base + t) (a.map (Row.shiftAfter r t)) := by
  intro i hi
  have hh : i < a.length := by simpa using hi
  have hv := row_shift_coreValid (r := r) (t := t) (h i hh)
  have hs : shiftAfter r t (base + i) = base + t + i := by
    simp only [shiftAfter, show r < base + i by omega, ↓reduceIte]
    omega
  simpa [hs] using hv

theorem coreValid_iff_block {a : Pattern} :
    (∀ r row, rowAt a r = some row → row.CoreValid r) ↔ BlockCoreValid 1 a := by
  constructor
  · intro h i hi
    have hr : rowAt a (i + 1) = some a[i] := by simp [rowAt, hi]
    simpa [Nat.add_comm] using h (i + 1) a[i] hr
  · intro h r row hr
    have hb := rowAt_bounds hr
    have hh : a[r - 1]? = some row := by simpa [rowAt, Nat.ne_of_gt hb.1] using hr
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hh
    have hv := h (r - 1) hi
    have hi' : 1 + (r - 1) = r := by omega
    simpa [he, hi'] using hv

/-- All old and new rows of a native output satisfy ordinary core validity. -/
theorem native_preserves_coreValid {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {sources : List Nat} (h : native a r = some (b, sources)) :
    ∀ owner row, rowAt b owner = some row → row.CoreValid owner := by
  obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ss, hs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨block, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨block', hb', hv⟩ := nativeBlock_actual_total valid hr hs
  have heq := Option.some.inj (hb.symm.trans hb')
  subst block'
  change some (_, ss) = some (b, sources) at h
  cases Option.some.inj h
  apply coreValid_iff_block.mpr
  have va := coreValid_iff_block.mp valid
  have hrb := rowAt_bounds hr
  have hpre : (a.take (r - 1)).length = r - 1 := by simp; omega
  have hblock := nativeBlock_length hb
  apply blockCoreValid_append
  · apply blockCoreValid_append (blockCoreValid_take va (r - 1))
    simpa [hpre, show 1 + (r - 1) = r by omega] using hv
  · have ht := blockCoreValid_shift (r := r) (t := sources.length)
      (blockCoreValid_drop va r) (by omega)
    have hidx : 1 + ((a.take (r - 1) ++ block).length) = (1 + r) + sources.length := by
      simp only [List.length_append, hpre, hblock]
      omega
    simpa only [hidx] using ht

end FullMarkedBLP
