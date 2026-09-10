import FullMarkedBLP.CopyHighTrace
import FullMarkedBLP.CopyMarks

namespace FullMarkedBLP

/-- The last word factor may be high even when the endpoint is below p. -/
theorem shortCopy_high_terminal_trace {a b : Pattern} {last : Row}
    {p e s y terminal s' y' : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hpt : p ≤ terminal) (hye : y < e) (hpn : p ≤ a.length)
    (hv : last.CoreValid a.length) (ht : Trace a s y xs)
    (hf : fromRight xs 2 = some terminal)
    (hs : copyEntry a.length last s = some s')
    (hy : copyEntry a.length last y = some y') : ∃ word, Trace b s' y' word := by
  induction ht generalizing y' with
  | stop => simp [fromRight] at hf
  | @next y z tail hsy hz ht ih =>
    have hb := trace_terminal_factor valid (Trace.next hsy hz ht) hf
    have hpy : p ≤ y := by omega
    have hy' := copyEntry_high_value hv hp hpy hy
    obtain ⟨z', hzmap, hz'⟩ := shortCopy_predecessor h hl hp he hpy hye hpn hz
    have hpred : predecessor b y' = some z' := by simpa only [hy'] using hz'
    have hs'y' := copyEntry_strict hv hsy hs hy
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons v rest =>
      cases rest with
      | nil =>
        have hvz : v = z := by simpa using trace_head ht
        have hvs : v = s := by simpa using trace_last ht
        have hzs : z = s := hvz.symm.trans hvs
        have heq : z' = s' := Option.some.inj ((hzs ▸ hzmap).symm.trans hs)
        subst z'
        exact ⟨[y', s'], Trace.next hs'y' hpred Trace.stop⟩
      | cons w rest =>
        have hf' : fromRight (v :: w :: rest) 2 = some terminal := by
          simpa only [fromRight_cons_of_le (by simp : 2 ≤ (v :: w :: rest).length)] using hf
        have hzy := predecessor_lt valid hz
        obtain ⟨word, hw⟩ := ih (by omega) hf' hzmap
        exact ⟨y' :: word, Trace.next hs'y' hpred hw⟩

theorem copiedRow_high_mark_trace {a b : Pattern} {last row copied : Row}
    {p e r k y x terminal : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hpt : p ≤ terminal) (hre : r ≤ e) (hpn : p ≤ a.length)
    (hv : last.CoreValid a.length) (hr : rowAt a r = some row)
    (hm : row.ProperMarks r) (hym : y ∈ row.marks)
    (hc : copiedRow a last r row = some copied)
    (hy : row.core[k]? = some y) (hx : copied.core[k]? = some x)
    (hcompute : computeMarkTrace a r y = some xs) (hf : fromRight xs 2 = some terminal) :
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
  obtain ⟨word, hw⟩ := shortCopy_high_terminal_trace valid h hl hp he hpt (by omega) hpn hv ht hf hsmap hxmap
  exact ⟨s', word, hj, hs', hw⟩

end FullMarkedBLP

