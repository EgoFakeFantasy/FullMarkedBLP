import FullMarkedBLP.CopyLowTrace

namespace FullMarkedBLP

/-- Join two actual predecessor chains at their common endpoint. -/
theorem trace_join {a : Pattern} {s t y : Nat} {front tail : List Nat}
    (hf : Trace a t y front) (ht : Trace a s t tail) :
    Trace a s y (front.dropLast ++ tail) := by
  have hst := trace_source_le_head ht
  induction hf with
  | stop => simpa using ht
  | @next y z rest hty hp hr ih =>
    have hn := trace_nonempty hr
    have he : (y :: rest).dropLast = y :: rest.dropLast := by
      cases rest with
      | nil => contradiction
      | cons v vs => rfl
    simpa only [he, List.cons_append] using Trace.next (by omega : s < y) hp ih

/-- Replace the low tail by a verified bridge, retaining the high copied prefix. -/
theorem shortCopy_trace_splice {a b : Pattern} {last : Row}
    {p e low low' s y s' y' : Nat} {xs bridge : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hye : y < e) (hpn : p ≤ a.length) (hv : last.CoreValid a.length)
    (ht : Trace a s y xs) (hf : xs.find? (· < p) = some low)
    (hs : copyEntry a.length last s = some s')
    (hy : copyEntry a.length last y = some y')
    (hlo : copyEntry a.length last low = some low')
    (hb : Trace b s' low' bridge) : ∃ word, Trace b s' y' word := by
  induction ht generalizing y' with
  | stop =>
    have hh := Option.some.inj (hs.symm.trans hy)
    subst y'
    exact ⟨[s'], Trace.stop⟩
  | @next y z tail hsy hz ht ih =>
    by_cases hyp : y < p
    · have hyl : y = low := by simpa [List.find?_cons, hyp] using hf
      have hh : y' = low' := Option.some.inj ((hyl ▸ hy).symm.trans hlo)
      subst y'
      exact ⟨bridge, hb⟩
    · have hf' : tail.find? (· < p) = some low := by
        simpa [List.find?_cons, hyp] using hf
      have hpy : p ≤ y := by omega
      obtain ⟨z', hzmap, hz'⟩ := shortCopy_predecessor h hl hp he hpy hye hpn hz
      have hy' := copyEntry_high_value hv hp hpy hy
      have hpred : predecessor b y' = some z' := by simpa only [hy'] using hz'
      have hzy := predecessor_lt valid hz
      obtain ⟨word, hw⟩ := ih (by omega) hf' hzmap
      exact ⟨y' :: word, Trace.next (copyEntry_strict hv hsy hs hy) hpred hw⟩

end FullMarkedBLP
