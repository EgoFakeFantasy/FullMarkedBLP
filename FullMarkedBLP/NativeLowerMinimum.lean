import FullMarkedBLP.NativeTopCritical

namespace FullMarkedBLP

theorem nativeLower_preserves_minimum {row lower : Row} {owner minimum : Nat} {medium : Bool}
    (hv : row.CoreValid owner) (hm : row.core.head? = some minimum)
    (hl : nativeLower row owner medium = some lower) : lower.core.head? = some minimum := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hm0 : row.core[0]? = some minimum := by simpa only [List.head?_eq_getElem?] using hm
  simpa only [List.head?_eq_getElem?] using
    nativeLower_keeps_low_entry hv (by omega : 0 < row.core.length - row.step) hm0 hl

end FullMarkedBLP
