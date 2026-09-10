import FullMarkedBLP.NativeMiddleSat

namespace FullMarkedBLP

theorem shifted_row_b (row : Row) (r t : Nat) :
    (row.shiftAfter r t).b = row.b.map (shiftAfter r t) :=
  fromRight_map _ _ _

theorem shiftAfter_le (r t : Nat) {x y : Nat} (h : x ≤ y) :
    shiftAfter r t x ≤ shiftAfter r t y := by
  by_cases he : x = y
  · subst y; exact Nat.le_refl _
  · exact Nat.le_of_lt (shiftAfter_strict r t (by omega))

/-- A suffix Sat witness transports whenever its endpoint avoids the replaced owner. -/
theorem native_suffix_sat_away_owner {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {owner r p e : Nat} {row : Row} {sources : List Nat}
    (hn : native a owner = some (b, sources))
    (hr : rowAt a r = some row) (howner : owner < r)
    (hp : row.p = some p) (he : row.e = some e) (hne : e ≠ owner)
    (hw : ∃ er v, rowAt a e = some er ∧ er.b = some v ∧ v ≤ p) :
    ∃ out er v, rowAt b (r + sources.length) = some out ∧
      out.p = some (shiftAfter owner sources.length p) ∧
      out.e = some (shiftAfter owner sources.length e) ∧
      rowAt b (shiftAfter owner sources.length e) = some er ∧
      er.b = some v ∧ v ≤ shiftAfter owner sources.length p := by
  obtain ⟨er, v, her, hb, hle⟩ := hw
  have hout : rowAt b (r + sources.length) = some (row.shiftAfter owner sources.length) := by
    simpa only [hr, Option.map_some] using native_suffix_rowAt hn howner
  have hpp : (row.shiftAfter owner sources.length).p = some (shiftAfter owner sources.length p) := by
    simp only [shifted_row_p, hp, Option.map_some]
  have hee : (row.shiftAfter owner sources.length).e = some (shiftAfter owner sources.length e) := by
    simp only [shifted_row_e, he, Option.map_some]
  by_cases hafter : owner < e
  · have her' : rowAt b (shiftAfter owner sources.length e) = some (er.shiftAfter owner sources.length) := by
      simpa only [shiftAfter, hafter, ↓reduceIte, her, Option.map_some] using native_suffix_rowAt hn hafter
    refine ⟨_, _, shiftAfter owner sources.length v, hout, hpp, hee, her', ?_, shiftAfter_le _ _ hle⟩
    simp only [shifted_row_b, hb, Option.map_some]
  · have heBefore : e < owner := by omega
    have hv := valid e er her
    have hvlt := fromRight_lt_last hv.1 hv.2.2.1 (by decide : 1 < 2) hb
    have hvfix : shiftAfter owner sources.length v = v := by simp [shiftAfter, show ¬ owner < v by omega]
    have her' : rowAt b (shiftAfter owner sources.length e) = some er := by
      simpa only [shiftAfter, hafter, ↓reduceIte] using (native_prefix_rowAt hn heBefore).trans her
    exact ⟨_, er, v, hout, hpp, hee, her', hb, by simpa only [hvfix] using shiftAfter_le owner sources.length hle⟩

end FullMarkedBLP
