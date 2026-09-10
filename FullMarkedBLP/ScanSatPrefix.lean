import FullMarkedBLP.CopyInternalSat

namespace FullMarkedBLP

/-- A local Sat witness depends only on rows no later than its owner. -/
theorem sat_witness_prefix {a b : Pattern} {row : Row} {r bound q : Nat}
    (hv : row.CoreValid r) (hr : r < bound)
    (earlier : ∀ i, i < bound → rowAt b i = rowAt a i)
    (hw : ∃ e er v, row.e = some e ∧ rowAt a e = some er ∧ er.b = some v ∧ v ≤ q) :
    ∃ e er v, row.e = some e ∧ rowAt b e = some er ∧ er.b = some v ∧ v ≤ q := by
  obtain ⟨e, er, v, he, her, hb, hle⟩ := hw
  have hbound := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
  exact ⟨e, er, v, he, (earlier e (by omega)).trans her, hb, hle⟩

theorem scan_step_preserves_earlier_sat {a b : Pattern} {rec : Records}
    {owner r q : Nat} {sources : List Nat} {row : Row}
    (hn : native (completeFrozenMarks a rec owner) owner = some (b, sources))
    (hv : row.CoreValid r) (hr : r < owner)
    (hw : ∃ e er v, row.e = some e ∧ rowAt a e = some er ∧ er.b = some v ∧ v ≤ q) :
    ∃ e er v, row.e = some e ∧ rowAt b e = some er ∧ er.b = some v ∧ v ≤ q :=
  sat_witness_prefix hv hr (fun _ hi => scan_step_prefix_rowAt hn hi) hw

/-- Earlier Sat witnesses remain valid during every prefix of the frozen-mark fold. -/
theorem frozen_fold_preserves_earlier_sat {a : Pattern} {rec : Records}
    {owner r q : Nat} {row : Row} (processed : List Nat)
    (hv : row.CoreValid r) (hr : r < owner)
    (hw : ∃ e er v, row.e = some e ∧ rowAt a e = some er ∧ er.b = some v ∧ v ≤ q) :
    ∃ e er v, row.e = some e ∧
      rowAt (processed.foldl (fun current y => completeMark current rec owner y) a) e = some er ∧
      er.b = some v ∧ v ≤ q :=
  sat_witness_prefix hv hr
    (fun _ hi => completeMarks_fold_other_row processed (by omega)) hw

theorem shortCopy_scan_old_prefix_rowAt {a copied current : Pattern} {rec : Records} {cursor i : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (hcopy : shortCopy a = some copied)
    (reach : ScanReach copied current rec cursor) (hi : i < a.length) :
    rowAt current i = rowAt a i := by
  induction reach with
  | start => exact shortCopy_prefix_rowAt hcopy hi
  | @next before after history owner sources previous hb hn ih =>
    by_cases howner : owner < a.length
    · obtain ⟨hbefore, hhistory⟩ := (shortCopy_scan_record_region valid hs hcopy previous).1 (by omega)
      subst before; subst history
      have hpositive := (scanReach_records_before previous).1
      obtain ⟨row, hr⟩ := rowAt_exists (a := a) hpositive (by omega)
      have hnative := shortCopy_sat_prefix_native valid hs hcopy hr howner
      have hn' : native copied owner = some (after, sources) := by
        simpa only [completeFrozenMarks_empty] using hn
      have heq := (Prod.mk.inj (Option.some.inj (hn'.symm.trans hnative))).1
      subst after
      exact shortCopy_prefix_rowAt hcopy hi
    · exact (scan_step_prefix_rowAt hn (by omega)).trans ih

theorem shortCopy_scan_old_sat {a copied current : Pattern} {rec : Records} {cursor r : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (hcopy : shortCopy a = some copied)
    (reach : ScanReach copied current rec cursor) {row : Row}
    (hr : rowAt current r = some row) (hbound : r < a.length)
    (heligible : row.core.length ≤ 2 * row.step) :
    ∃ p e er v, row.p = some p ∧ row.e = some e ∧ rowAt current e = some er ∧ er.b = some v ∧ v ≤ p := by
  have hold : rowAt a r = some row := (shortCopy_scan_old_prefix_rowAt valid hs hcopy reach hbound).symm.trans hr
  obtain ⟨p, e, er, v, hp, he, her, hb, hle⟩ := hs r row hold heligible
  have hv := valid r row hold
  have heBound := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
  exact ⟨p, e, er, v, hp, he,
    (shortCopy_scan_old_prefix_rowAt valid hs hcopy reach (by omega)).trans her, hb, hle⟩

end FullMarkedBLP


