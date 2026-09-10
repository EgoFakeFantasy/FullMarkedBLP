import FullMarkedBLP.CopyMiddleBridge
import FullMarkedBLP.CopyGuard

namespace FullMarkedBLP

theorem trace_member_le_head {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s y v : Nat} {xs : List Nat} (ht : Trace a s y xs) (hm : v ∈ xs) : v ≤ y := by
  induction ht with
  | stop => have he : v = s := by simpa using hm
            omega
  | @next y z rest hsy hp hr ih =>
    rcases List.mem_cons.mp hm with he | hm
    · omega
    · have hh := ih hm
      have hz := predecessor_lt valid hp
      omega

theorem copiedRow_middle_mark_trace {a b : Pattern} {last row copied : Row}
    {p e r k y x minimum low jlow shifted : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hminimum : last.core.head? = some minimum) (hlow : minimum ≤ low)
    (hmarks : last.ProperMarks a.length) (htraces : last.HasTraces a)
    (hmark : shifted ∈ last.marks) (hlo : last.core[jlow]? = some low)
    (hshift : last.core[jlow + last.step]? = some shifted)
    (hguard : copyPositionGuard copied.core row.step k minimum = true)
    (hre : r ≤ e) (hpn : p ≤ a.length)
    (hv : last.CoreValid a.length) (hr : rowAt a r = some row)
    (hm : row.ProperMarks r) (hym : y ∈ row.marks)
    (hc : copiedRow a last r row = some copied)
    (hy : row.core[k]? = some y) (hx : copied.core[k]? = some x)
    (hcompute : computeMarkTrace a r y = some xs) (hf : xs.find? (· < p) = some low) :
    ∃ s' word, copied.step ≤ k ∧ copied.core[k - copied.step]? = some s' ∧ Trace b s' x word := by
  obtain ⟨old, j, s, hold, _, hj, hjy, hjs, ht⟩ := computeMarkTrace_sound hr hym hcompute
  have hold' := Option.some.inj (hold.symm.trans hr)
  subst old
  have hkj : k = j := Option.some.inj ((sorted_findIdx (valid r row hr).1 hy).symm.trans
    (sorted_findIdx (valid r row hr).1 hjy))
  subst j
  obtain ⟨core, hcore, hout⟩ := Option.bind_eq_some_iff.mp hc
  have hstruct := Option.some.inj hout
  cases hstruct
  obtain ⟨s', hs', hsmap⟩ := (copiedCore_maps_entries hcore).at_left hjs
  obtain ⟨original, horig, hxmap⟩ := (copiedCore_maps_entries hcore).at hx
  have horig' := Option.some.inj (horig.symm.trans hy)
  subst original
  have hylt := (hm.2 y hym).1
  have hsmin := copyPositionGuard_source_lt (copiedCore_sorted hv (valid r row hr) hcore) hj hs' hguard
  have hlowy := trace_member_le_head valid ht (List.mem_of_find?_eq_some hf)
  obtain ⟨word, hw⟩ := shortCopy_middle_trace valid h hl hp he hminimum hlow (by omega) (by omega) hpn hv hmarks htraces hmark hlo hshift ht hf hsmap hsmin hxmap
  exact ⟨s', word, hj, hs', hw⟩



/-- All three actual mark-retention branches yield traces in the copied pattern. -/
theorem copiedRow_hasTraces {a b : Pattern} {last row copied : Row} {r e : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (he : last.e = some e) (hre : r ≤ e)
    (hv : last.CoreValid a.length) (hmarks : last.ProperMarks a.length)
    (htraces : last.HasTraces a) (hr : rowAt a r = some row)
    (hm : row.ProperMarks r) (hc : copiedRow a last r row = some copied) :
    copied.HasTraces b := by
  intro x hx
  obtain ⟨k, y, hym, hky, hkx, _, hguard⟩ := copiedRow_mark_origin hc hx
  obtain ⟨last', minimum, p, xs, terminal, hl', hmin, hp, hcompute, hf, hcases⟩ := copyMarkAllowed_cases hguard
  have hlast := Option.some.inj (hl'.symm.trans hl)
  subst last'
  have hpn := fromRight_le_last hv.1 hv.2.2.1 (by omega : 0 < last.step + 1) hp
  have result : ∃ s word, copied.step ≤ k ∧ copied.core[k - copied.step]? = some s ∧ Trace b s x word := by
    rcases hcases with hhigh | ⟨_, low, hlow, hcases⟩
    · exact copiedRow_high_mark_trace valid h hl hp he hhigh hre hpn hv hr hm hym hc hky hkx hcompute hf
    · rcases hcases with hsmall | ⟨hmiddle, j, shifted, hj, hshift, hmark, hposition⟩
      · exact copiedRow_low_mark_trace valid h hl hp he hmin hsmall hre hpn hv hr hm hym hc hky hkx hcompute hlow
      · obtain ⟨hjbound, hjvalue, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
        have hjlow : last.core[j]? = some low := by
          apply List.getElem?_eq_some_iff.mpr
          exact ⟨hjbound, by simpa using hjvalue⟩
        exact copiedRow_middle_mark_trace valid h hl hp he hmin hmiddle hmarks htraces hmark hjlow hshift hposition hre hpn hv hr hm hym hc hky hkx hcompute hlow
  obtain ⟨s, word, hs, hsource, ht⟩ := result
  exact ⟨k, s, word, hs, hkx, hsource, ht⟩

end FullMarkedBLP


