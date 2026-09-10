import FullMarkedBLP.NativeBottomBExact

namespace FullMarkedBLP

/-- B transports under native for every old index, including the expanded owner. -/
theorem native_b_shift {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r i v : Nat} {sources : List Nat} {row : Row}
    (birth : native a r = some (b, sources)) (hr : rowAt a i = some row)
    (hb : row.b = some v) :
    (rowAt b (shiftAfter r sources.length i)).bind Row.b = some (shiftAfter r sources.length v) := by
  have vi := native_source_lt valid hr hb
  by_cases eq : i = r
  · subst i
    have bounds := rowAt_bounds hr
    have len := native_length birth
    obtain ⟨bottom, atBottom⟩ := rowAt_exists (a := b) bounds.1 (by omega)
    have result := native_bottom_b_eq valid hr birth atBottom hb
    simpa only [shiftAfter, show ¬ r < r by omega, show ¬ r < v by omega,
      if_false, atBottom, Option.bind_some] using result
  · by_cases before : i < r
    · have fixed := native_prefix_rowAt birth before
      simp only [shiftAfter, show ¬ r < i by omega, show ¬ r < v by omega, if_false,
        fixed, hr, Option.bind_some, hb]
    · have after : r < i := by omega
      rw [show shiftAfter r sources.length i = i + sources.length by simp [shiftAfter, after],
        native_suffix_rowAt birth after, hr]
      simp only [Option.map_some, Option.bind_some, shifted_row_b, hb, Option.map_some]

end FullMarkedBLP
