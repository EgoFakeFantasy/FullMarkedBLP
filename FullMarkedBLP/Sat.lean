import FullMarkedBLP.NativeTermination

namespace FullMarkedBLP

theorem sat_nativeSources_empty {a : Pattern} (hs : Sat a)
    {r : Nat} {row : Row} (hr : rowAt a r = some row) :
    nativeSources a r = some [] := by
  by_cases hl : 2 * row.step < row.core.length
  · simp [nativeSources, hr, hl]
  · obtain ⟨p, e, er, b, hp, he, her, hb, hle⟩ := hs r row hr (by omega)
    simp [nativeSources, hr, hl, hp, he, nativeSourcesFuel, her, hb, Nat.not_lt.mpr hle]

theorem row_shift_zero (row : Row) (r : Nat) : row.shiftAfter r 0 = row := by
  have hf : FullMarkedBLP.shiftAfter r 0 = id := by
    funext x; simp [FullMarkedBLP.shiftAfter]
  cases row
  simp [Row.shiftAfter, hf]

theorem rowAt_reconstruct {a : Pattern} {r : Nat} {row : Row}
    (hr : rowAt a r = some row) :
    a.take (r - 1) ++ [row] ++ a.drop r = a := by
  have hb := rowAt_bounds hr
  have hh : a[r - 1]? = some row := by simpa [rowAt, Nat.ne_of_gt hb.1] using hr
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hh
  have hs := List.set_getElem_self hi
  rw [he, List.set_eq_take_append_cons_drop, if_pos hi] at hs
  have hn : r - 1 + 1 = r := by omega
  simpa [hn, List.append_assoc] using hs

theorem native_empty {a : Pattern} {r : Nat} {row : Row}
    (hr : rowAt a r = some row) (hs : nativeSources a r = some []) :
    native a r = some (a, []) := by
  have hf : Row.shiftAfter r 0 = id := funext (fun row => row_shift_zero row r)
  simpa [native, hr, hs, nativeBlock, hf, List.append_assoc] using congrArg
    (fun b => some (b, ([] : List Nat))) (rowAt_reconstruct hr)

theorem sat_native_identity {a : Pattern} (hs : Sat a)
    {r : Nat} {row : Row} (hr : rowAt a r = some row) :
    native a r = some (a, []) := native_empty hr (sat_nativeSources_empty hs hr)

theorem completionRecord_empty (a : Pattern) (r y : Nat) :
    completionRecord a [] r y = none := by
  simp [completionRecord, recordAt]

theorem completeMark_empty (a : Pattern) (r y : Nat) :
    completeMark a [] r y = a := by
  simp [completeMark, completionRecord_empty]


theorem completeFrozenMarks_empty (a : Pattern) (r : Nat) :
    completeFrozenMarks a [] r = a := by
  unfold completeFrozenMarks
  split
  · rfl
  · simp only [completeMark_empty]
    rename_i row heq
    generalize row.marks = marks
    induction marks with
    | nil => rfl
    | cons y ys ih => exact ih


/-- With empty records, scanning a Sat pattern is literally stationary. -/
theorem sat_scan_identity {a : Pattern} (hs : Sat a) (fuel : Nat) :
    ∀ r, 0 < r → a.length + 1 - r ≤ fuel → scanFuel fuel a [] r = some a := by
  induction fuel with
  | zero =>
    intro r hr hf
    have hb : a.length < r := by omega
    simp [scanFuel, hb]
  | succ fuel ih =>
    intro r hr hf
    by_cases hb : a.length < r
    · simp [scanFuel, hb]
    · obtain ⟨row, he⟩ := rowAt_exists (a := a) hr (by omega)
      have hn := sat_native_identity hs he
      have hh := ih (r + 1) (by omega) (by omega)
      simpa [scanFuel, hb, completeFrozenMarks_empty, hn] using hh

theorem sat_fullScan_identity {a : Pattern} (hs : Sat a) : fullScan a = some a :=
  sat_scan_identity hs a.length 1 (by decide) (by omega)

end FullMarkedBLP
