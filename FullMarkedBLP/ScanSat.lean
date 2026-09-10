import FullMarkedBLP.NativeSat

namespace FullMarkedBLP

def SatBelow (a : Pattern) (bound : Nat) : Prop :=
  ∀ i row, i < bound → rowAt a i = some row → row.core.length ≤ 2 * row.step →
    ∃ p e er v, row.p = some p ∧ row.e = some e ∧ rowAt a e = some er ∧ er.b = some v ∧ v ≤ p

theorem native_advances_sat_prefix {a b : Pattern}
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    {r : Nat} {sources : List Nat} (hs : SatBelow a r)
    (hn : native a r = some (b, sources)) : SatBelow b (r + sources.length + 1) := by
  obtain ⟨old, hold, _⟩ := Option.bind_eq_some_iff.mp hn
  have hsrc := native_sources_of_success hn
  intro i row hib hi heligible
  by_cases hbefore : i < r
  · have ha := (native_prefix_rowAt hn hbefore).symm.trans hi
    obtain ⟨p, e, er, v, hp, he, her, hb, hle⟩ := hs i row hbefore ha heligible
    have hv := valid i row ha
    have heBound := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
    exact ⟨p, e, er, v, hp, he, (native_prefix_rowAt hn (by omega)).trans her, hb, hle⟩
  · by_cases hnil : sources = []
    · subst sources
      have hir : i = r := by simp only [List.length_nil] at hib; omega
      subst i
      have hid := native_empty hold hsrc
      have heq := (Prod.mk.inj (Option.some.inj (hn.symm.trans hid))).1
      subst b
      exact nativeSources_empty_local_sat (valid r row hi) hi heligible hsrc
    · have hv := valid r old hold
      have hroom := Row.step_lt_length hv.2.2.2
      obtain ⟨p, hp⟩ := fromRight_exists (xs := old.core) (k := old.step + 1) (by omega) (by omega)
      obtain ⟨e, he⟩ := fromRight_exists (xs := old.core) (k := old.step) hv.2.2.2.1 (by omega)
      obtain ⟨out, q, endpoint, er, v, hout, hq, hep, her, hb, hle⟩ :=
        native_block_sat_witness valid hold hp he hsrc hnil hn (show i - r ≤ sources.length by omega)
      have hout' : rowAt b i = some out := by simpa only [show r + (i - r) = i by omega] using hout
      have heq := Option.some.inj (hout'.symm.trans hi)
      subst out
      exact ⟨q, endpoint, er, v, hq, hep, her, hb, hle⟩

theorem completeFrozenMarks_preserves_sat_prefix {a : Pattern} {rec : Records} {r : Nat}
    (valid : ∀ i row, rowAt (completeFrozenMarks a rec r) i = some row → row.CoreValid i)
    (hs : SatBelow a r) : SatBelow (completeFrozenMarks a rec r) r := by
  intro i row hib hi heligible
  have ha : rowAt a i = some row := (completeFrozenMarks_other_row (by omega : i ≠ r)).symm.trans hi
  obtain ⟨p, e, er, v, hp, he, her, hb, hle⟩ := hs i row hib ha heligible
  have hv := valid i row hi
  have heBound := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
  exact ⟨p, e, er, v, hp, he, (completeFrozenMarks_other_row (by omega : e ≠ r)).trans her, hb, hle⟩

theorem scanReach_sat_prefix {initial current : Pattern} {rec : Records} {cursor : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial current rec cursor) : SatBelow current cursor := by
  induction reach with
  | start =>
    intro i row hib hi _
    have hpos := (rowAt_bounds hi).1
    omega
  | @next before after history owner sources previous hb hn ih =>
    have hv := historyValid before history owner previous
    exact native_advances_sat_prefix hv (completeFrozenMarks_preserves_sat_prefix hv ih) hn

/-- Successful full scans are Sat once actual intermediate row legality is established. -/
theorem fullScan_sat_of_history_valid {a b : Pattern}
    (historyValid : ∀ before history owner, ScanReach a before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (h : fullScan a = some b) : Sat b := by
  obtain ⟨rec, cursor, reach, hbound, _⟩ := fullScan_reaches_end h
  have hs := scanReach_sat_prefix historyValid reach
  intro i row hi heligible
  have hib := (rowAt_bounds hi).2
  exact hs i row (by omega) hi heligible

end FullMarkedBLP
