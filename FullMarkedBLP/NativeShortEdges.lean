import FullMarkedBLP.NativeShortFull

namespace FullMarkedBLP

theorem nativeLower_short_realizes_edges {alpha : Type u} {row lower : Row} {owner : Nat}
    (action : alpha → alpha) (theta : Nat → alpha)
    (hv : row.CoreValid owner) (ho : 0 < owner)
    (hlen : row.core.length + 1 = 2 * row.step)
    (hs : 1 < row.step) (hl : nativeLower row owner false = some lower)
    (hedges : row.RealizesEdges action theta owner) :
    lower.RealizesEdges action theta (owner - 1) := by
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step)
    hv.2.2.2.1 (Row.step_lt_length hv.2.2.2).le
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [fromRight, hv.2.2.2.1, (Row.step_lt_length hv.2.2.2).le] using he
  have hem := List.mem_of_getElem? hei
  have hstep := nativeLower_step hl
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  intro k x y hx hy
  rw [nativeLower_short_full hv ho hs he hl] at hx hy
  rw [hstep] at hy
  have hyb := (List.getElem?_eq_some_iff.mp hy).1
  rw [List.length_erase_of_mem hem] at hyb
  have hk : k < row.core.length - row.step := by omega
  have hkl : k < row.core.length := by omega
  have htl : k + row.step < row.core.length := by omega
  let u := row.core[k]'hkl
  let v := row.core[k + row.step]'htl
  have hu : row.core[k]? = some u := List.getElem?_eq_getElem hkl
  have hv' : row.core[k + row.step]? = some v := List.getElem?_eq_getElem htl
  have heiBound := (List.getElem?_eq_some_iff.mp hei).1
  have hue : u < e := by
    have hh := List.pairwise_iff_getElem.mp hv.1 k (row.core.length - row.step) hkl heiBound hk
    simpa only [(List.getElem?_eq_some_iff.mp hei).2] using hh
  have hev : e < v := by
    have hh := List.pairwise_iff_getElem.mp hv.1 (row.core.length - row.step) (k + row.step)
      heiBound htl (by omega)
    simpa only [(List.getElem?_eq_some_iff.mp hei).2] using hh
  have hux := erase_greater_preserves_index hv.1 hu hue
  have hvy := erase_smaller_preserves_index hv.1 hv' hem hev
  have hidx : k + row.step - 1 = k + (row.step - 1) := by omega
  rw [hidx] at hvy
  have hxu : u = x := Option.some.inj (hux.symm.trans hx)
  have hyv : v = y := Option.some.inj (hvy.symm.trans hy)
  subst x
  subst y
  exact hedges k u v (full_entry_of_core hu) (full_entry_of_core hv')

end FullMarkedBLP
