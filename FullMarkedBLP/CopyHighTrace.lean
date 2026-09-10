import FullMarkedBLP.CopyPredecessor
import FullMarkedBLP.PacketChains

namespace FullMarkedBLP

/-- A trace whose endpoint stays above the threshold is translated throughout. -/
theorem shortCopy_high_trace {a b : Pattern} {last : Row} {p e s y : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hps : p ≤ s) (hye : y < e) (hpn : p ≤ a.length)
    (hv : last.CoreValid a.length) (ht : Trace a s y xs) :
    Trace b (s + (a.length - p)) (y + (a.length - p))
      (xs.map (fun x => x + (a.length - p))) := by
  induction ht with
  | stop => exact Trace.stop
  | @next y z tail hsy hz ht ih =>
    have hsz := trace_source_le_head ht
    have hzy := predecessor_lt valid hz
    obtain ⟨q, hq, hb⟩ := shortCopy_predecessor h hl hp he (by omega) hye hpn hz
    have hqeq := copyEntry_high_value hv hp (by omega : p ≤ z) hq
    apply Trace.next (by omega)
    · simpa only [hqeq] using hb
    · exact ih (by omega)

end FullMarkedBLP
