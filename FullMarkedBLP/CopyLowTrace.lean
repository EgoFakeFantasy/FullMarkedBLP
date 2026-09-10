import FullMarkedBLP.CopyTerminalTrace
import FullMarkedBLP.CopyPrefixTrace

namespace FullMarkedBLP

theorem copyEntry_low_value {n minimum x v : Nat} {row : Row}
    (hm : row.core.head? = some minimum) (hx : x < minimum)
    (h : copyEntry n row x = some v) : v = x := by
  obtain ⟨minimum', p, e, hm', _, _, _, _, hc⟩ := copyEntry_cases h
  have hh := Option.some.inj (hm'.symm.trans hm)
  subst minimum'
  rcases hc with ⟨_, he⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩
  · exact he
  · omega
  · omega

/-- After the first below-p factor falls below the minimum, the old tail survives. -/
theorem shortCopy_low_trace {a b : Pattern} {last : Row}
    {p e minimum low s y s' y' : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hm : last.core.head? = some minimum) (hlo : low < minimum)
    (hye : y < e) (hpn : p ≤ a.length)
    (hv : last.CoreValid a.length) (ht : Trace a s y xs)
    (hf : xs.find? (· < p) = some low)
    (hs : copyEntry a.length last s = some s')
    (hy : copyEntry a.length last y = some y') : ∃ word, Trace b s' y' word := by
  induction ht generalizing y' with
  | stop =>
    have hh := Option.some.inj (hs.symm.trans hy)
    subst y'
    exact ⟨[s'], Trace.stop⟩
  | @next y z tail hsy hz ht ih =>
    by_cases hyp : y < p
    · have hyl : y = low := by simpa [List.find?_cons, hyp] using hf
      have hymin : y < minimum := by omega
      have hsmin : s < minimum := by omega
      have hyy := copyEntry_low_value hm hymin hy
      have hss := copyEntry_low_value hm hsmin hs
      subst y'; subst s'
      exact ⟨y :: tail, shortCopy_prefix_trace valid h (Trace.next hsy hz ht) (by omega)⟩
    · have hf' : tail.find? (· < p) = some low := by
        simpa [List.find?_cons, hyp] using hf
      have hpy : p ≤ y := by omega
      obtain ⟨z', hzmap, hz'⟩ := shortCopy_predecessor h hl hp he hpy hye hpn hz
      have hy' := copyEntry_high_value hv hp hpy hy
      have hpred : predecessor b y' = some z' := by simpa only [hy'] using hz'
      have hzy := predecessor_lt valid hz
      obtain ⟨word, hw⟩ := ih (by omega) hf' hzmap
      exact ⟨y' :: word, Trace.next (copyEntry_strict hv hsy hs hy) hpred hw⟩

theorem copiedRow_low_mark_trace {a b : Pattern} {last row copied : Row}
    {p e r k y x minimum low : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hminimum : last.core.head? = some minimum) (hlow : low < minimum)
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
  obtain ⟨word, hw⟩ := shortCopy_low_trace valid h hl hp he hminimum hlow (by omega) hpn hv ht hf hsmap hxmap
  exact ⟨s', word, hj, hs', hw⟩


end FullMarkedBLP

