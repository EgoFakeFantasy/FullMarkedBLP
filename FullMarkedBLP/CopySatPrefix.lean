import FullMarkedBLP.CopyTraceClosure
import FullMarkedBLP.Sat

namespace FullMarkedBLP

theorem shortCopy_sat_prefix_native {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (h : shortCopy a = some b)
    {r : Nat} {row : Row} (hr : rowAt a r = some row) (hbound : r < a.length) :
    native b r = some (b, []) := by
  have hrb : rowAt b r = some row := (shortCopy_prefix_rowAt h hbound).trans hr
  apply native_empty hrb
  by_cases hlong : 2 * row.step < row.core.length
  · simp [nativeSources, hrb, hlong]
  · obtain ⟨p, e, er, eb, hp, he, her, heb, hle⟩ := hs r row hr (by omega)
    have hv := valid r row hr
    have heBound := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
    have her' : rowAt b e = some er := (shortCopy_prefix_rowAt h (by omega)).trans her
    simp [nativeSources, hrb, hlong, hp, he, nativeSourcesFuel, her', heb, Nat.not_lt.mpr hle]

/-- The scan traverses the inherited prefix without modifying it or creating records. -/
theorem shortCopy_sat_prefix_scan {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (h : shortCopy a = some b) {cursor : Nat}
    (hpos : 0 < cursor) (hcursor : cursor ≤ a.length) : ScanReach b b [] cursor := by
  induction cursor with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst n; exact ScanReach.start
    · have hnp : 0 < n := by omega
      have reach := ih hnp (by omega)
      obtain ⟨row, hr⟩ := rowAt_exists (a := a) hnp (by omega)
      have hrow : rowAt b n = some row := (shortCopy_prefix_rowAt h (by omega)).trans hr
      have hbound := (rowAt_bounds hrow).2
      have hnative := shortCopy_sat_prefix_native valid hs h hr (by omega)
      have hstep : native (completeFrozenMarks b [] n) n = some (b, []) := by
        simpa only [completeFrozenMarks_empty] using hnative
      simpa using ScanReach.next reach hbound hstep

theorem shortCopy_sat_scanFuel_skip {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (h : shortCopy a = some b) (steps fuel : Nat) {cursor : Nat}
    (hpos : 0 < cursor) (hcursor : cursor + steps ≤ a.length) :
    scanFuel (steps + fuel) b [] cursor = scanFuel fuel b [] (cursor + steps) := by
  induction steps generalizing cursor with
  | zero => simp
  | succ steps ih =>
    obtain ⟨row, hr⟩ := rowAt_exists (a := a) hpos (by omega)
    have hrow : rowAt b cursor = some row := (shortCopy_prefix_rowAt h (by omega)).trans hr
    have hbound := (rowAt_bounds hrow).2
    have hnative := shortCopy_sat_prefix_native valid hs h hr (by omega)
    rw [Nat.succ_add]
    simp only [scanFuel, show ¬b.length < cursor by omega, ↓reduceIte,
      completeFrozenMarks_empty, hnative]
    have hh := ih (cursor := cursor + 1) (by omega) (by omega)
    simpa only [show cursor + 1 + steps = cursor + (steps + 1) by omega] using hh

end FullMarkedBLP


