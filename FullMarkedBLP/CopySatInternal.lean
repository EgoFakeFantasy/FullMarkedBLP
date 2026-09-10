import FullMarkedBLP.CopySatWitness

namespace FullMarkedBLP

theorem row_p_lt_e {row : Row} {r p e : Nat}
    (hv : row.CoreValid r) (hp : row.p = some p) (he : row.e = some e) : p < e := by
  have hlen := Row.step_lt_length hv.2.2.2
  have hstep := hv.2.2.2.1
  have hp' : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have he' : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hstep, show row.step ≤ row.core.length by omega] using he
  obtain ⟨hi, hip⟩ := List.getElem?_eq_some_iff.mp hp'
  obtain ⟨hj, hje⟩ := List.getElem?_eq_some_iff.mp he'
  have hh := List.pairwise_iff_getElem.mp hv.1 _ _ hi hj (by omega)
  simpa only [hip, hje] using hh

/-- An internal high predecessor forces its Sat endpoint into the same copied interval. -/
theorem shortCopy_sat_high_predecessor {a b : Pattern} {last row copied : Row}
    {r predecessorValue threshold upper : Nat}
    (hs : Sat a) (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some threshold) (he : last.e = some upper)
    (hv : last.CoreValid a.length) (hrow : row.CoreValid r)
    (hr : rowAt a r = some row) (hc : copiedRow a last r row = some copied)
    (heligible : row.core.length ≤ 2 * row.step)
    (hpred : row.p = some predecessorValue) (hhigh : threshold ≤ predecessorValue)
    (hrange : r < upper) :
    ∃ p' e' er' v', copied.p = some p' ∧ copied.e = some e' ∧
      rowAt b e' = some er' ∧ er'.b = some v' ∧ v' ≤ p' := by
  have htn := fromRight_le_last hv.1 hv.2.2.1 (by omega : 0 < last.step + 1) hp
  apply shortCopy_sat_copied_endpoint hs h hl hp he hv htn hr hc heligible
  intro e hre
  have hpe := row_p_lt_e hrow hpred hre
  have her := fromRight_le_last hrow.1 hrow.2.2.1 hrow.2.2.2.1 hre
  constructor <;> omega

theorem copyEntry_high_region_iff {last : Row} {n p x v : Nat}
    (hv : last.CoreValid n) (hp : last.p = some p)
    (h : copyEntry n last x = some v) : n ≤ v ↔ p ≤ x := by
  have hpn := fromRight_le_last hv.1 hv.2.2.1 (by omega : 0 < last.step + 1) hp
  constructor
  · intro hnv
    obtain ⟨minimum, p', e, hm, hp', _, _, _, hc⟩ := copyEntry_cases h
    have hpp := Option.some.inj (hp'.symm.trans hp)
    subst p'
    rcases hc with ⟨hlo, hval⟩ | ⟨_, hhigh, _⟩ | ⟨_, hlow, k, hk, hkv⟩
    · have hmi : last.core[0]? = some minimum := by simpa [List.head?_eq_getElem?] using hm
      have hmin := core_entry_le_owner hv (List.mem_of_getElem? hmi)
      omega
    · exact hhigh
    · have hlt := copy_middle_below_owner hv hp hlow hk hkv
      omega
  · intro hpx
    have heq := copyEntry_high_value hv hp hpx h
    omega

/-- The copied row's visible high predecessor suffices for endpoint Sat transport. -/
theorem shortCopy_sat_output_predecessor {a b : Pattern} {last row copied : Row}
    {r q threshold upper : Nat}
    (hs : Sat a) (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some threshold) (he : last.e = some upper)
    (hv : last.CoreValid a.length) (hrow : row.CoreValid r)
    (hr : rowAt a r = some row) (hc : copiedRow a last r row = some copied)
    (heligible : row.core.length ≤ 2 * row.step)
    (hq : copied.p = some q) (hhigh : a.length ≤ q) (hrange : r < upper) :
    ∃ p' e' er' v', copied.p = some p' ∧ copied.e = some e' ∧
      rowAt b e' = some er' ∧ er'.b = some v' ∧ v' ≤ p' := by
  have hlen := Row.step_lt_length hrow.2.2.2
  obtain ⟨p, hrp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  obtain ⟨q', hq', hmap⟩ := copiedRow_p hrp hc
  have heq := Option.some.inj (hq'.symm.trans hq)
  subst q'
  have hpre := (copyEntry_high_region_iff hv hp hmap).mp hhigh
  exact shortCopy_sat_high_predecessor hs h hl hp he hv hrow hr hc heligible hrp hpre hrange

end FullMarkedBLP

