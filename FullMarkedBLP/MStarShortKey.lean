import FullMarkedBLP.NativeShortKey
import FullMarkedBLP.ExpansionShortKey
import FullMarkedBLP.GeneratedReachability

namespace FullMarkedBLP

theorem scanRun_earlier_rowAt {a b : Pattern} {rec : Records} {cursor i : Nat}
    (run : ScanRun a rec cursor b) (before : i < cursor) : rowAt b i = rowAt a i := by
  induction run with
  | done => rfl
  | next bound birth rest ih =>
    exact (ih (by omega)).trans (scan_step_prefix_rowAt birth before)

/-- Sat skips precisely the inherited prefix with empty records. The first
copied row is then processed by native, whose first key is unchanged, and
all subsequent scan events occur strictly to its right. -/
theorem shortCopy_fullScan_first_shortKey_lt {a copied b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r) (sat : Sat a)
    (copy : shortCopy a = some copied) (scan : fullScan copied = some b) :
    ∃ last bottom, a.getLast? = some last ∧ rowAt b a.length = some bottom ∧
      bottom.shortKey < last.shortKey := by
  obtain ⟨last, p, e, lastAt, hp, he⟩ := shortCopy_parameters copy
  have size := (rowAt_bounds lastAt).1
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg (by omega : a.length ≠ 0), List.getLast?_eq_getElem?] using lastAt
  have lastValid := valid _ _ lastAt
  have pe := row_p_lt_e lastValid hp he
  have pn := fromRight_le_last lastValid.1 lastValid.2.2.1 (by omega) hp
  obtain ⟨row, first, sourceAt, firstCopy, firstAt⟩ :=
    shortCopy_copied_rowAt copy lastGet hp he (Nat.le_refl _) pe pn
  have ownerEq : p + (a.length - p) = a.length := by omega
  rw [ownerEq] at firstAt
  have firstSmaller := copied_first_shortKey_lt lastValid (valid _ _ sourceAt) hp firstCopy
  have enough := (rowAt_bounds firstAt).2
  have skipped := shortCopy_sat_scanFuel_skip valid sat copy (a.length - 1)
    (copied.length - (a.length - 1)) (cursor := 1) (by omega) (by omega)
  have fuelEq : a.length - 1 + (copied.length - (a.length - 1)) = copied.length := by omega
  have cursorEq : 1 + (a.length - 1) = a.length := by omega
  rw [fuelEq, cursorEq] at skipped
  have remaining : scanFuel (copied.length - (a.length - 1)) copied [] a.length = some b :=
    skipped.symm.trans scan
  have nextFuel : copied.length - (a.length - 1) = (copied.length - a.length) + 1 := by omega
  rw [nextFuel] at remaining
  simp only [scanFuel, show ¬copied.length < a.length by omega, if_false,
    completeFrozenMarks_empty] at remaining
  obtain ⟨⟨next, sources⟩, birth, finish⟩ := Option.bind_eq_some_iff.mp remaining
  obtain ⟨bottom, atBottom, keyEq⟩ := native_bottom_shortKey
    (shortCopy_preserves_coreValid valid copy) firstAt birth
  have preserved := scanRun_earlier_rowAt (scanFuel_sound finish)
    (by omega : a.length < a.length + sources.length + 1)
  exact ⟨last, bottom, lastGet, preserved.trans atBottom, keyEq ▸ firstSmaller⟩

theorem mStar_shortKey_lt {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r) (sat : Sat a)
    (run : mStar a = some b) : shortKey b < shortKey a := by
  have initial := mStar_cut_prefix valid sat run
  unfold mStar at run
  split at run
  next =>
    obtain ⟨copied, copy, scan⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨last, bottom, lastGet, atBottom, smaller⟩ :=
      shortCopy_fullScan_first_shortKey_lt valid sat copy scan
    exact shortKey_lt_of_cut_prefix lastGet initial atBottom smaller
  next => simp at run

theorem step_shortKey_lt {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r) (sat : Sat a)
    (step : Step a b) : shortKey b < shortKey a := by
  cases step with
  | cut h => exact cut_shortKey_lt h
  | expand positive h => exact expand_shortKey_lt valid positive h
  | marked h => exact mStar_shortKey_lt valid sat h

theorem rankI2_generated_step_shortKey_lt (i2 : RankI2.{u}) {a b : Pattern}
    (generated : Generated a) (step : Step a b) : shortKey b < shortKey a := by
  obtain ⟨valid, sat⟩ := rankI2_generated_valid_sat i2 generated
  exact step_shortKey_lt valid sat step

end FullMarkedBLP
