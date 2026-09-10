import FullMarkedBLP.CopyMapCases

namespace FullMarkedBLP

theorem sorted_index_lt_of_value_lt {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {i j x y : Nat} (hx : xs[i]? = some x) (hy : xs[j]? = some y) (hxy : x < y) : i < j := by
  obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hy
  by_cases he : i = j
  · subst j; omega
  · by_cases hji : j < i
    · have hh := List.pairwise_iff_getElem.mp hs j i hj hi hji
      omega
    · omega

theorem copy_middle_below_owner {n p x v k : Nat} {row : Row}
    (hv : row.CoreValid n) (hp : row.p = some p) (hxp : x < p)
    (hx : row.core[k]? = some x) (hval : row.core[k + row.step]? = some v) : v < n := by
  have hl := Row.step_lt_length hv.2.2.2
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hk := sorted_index_lt_of_value_lt hv.1 hx hpi hxp
  have hend : row.core[row.core.length - 1]? = some n := by
    simpa [List.getLast?_eq_getElem?] using hv.2.2.1
  obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp hval
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hend
  have hh := List.pairwise_iff_getElem.mp hv.1 (k + row.step) (row.core.length - 1) hi hj (by omega)
  omega

theorem copyEntry_strict {n x y vx vy : Nat} {row : Row}
    (hv : row.CoreValid n) (hxy : x < y)
    (hx : copyEntry n row x = some vx) (hy : copyEntry n row y = some vy) : vx < vy := by
  have hyn := copyEntry_not_below_input hv hy
  obtain ⟨minimum, p, e, hm, hp, he, _, _, hxc⟩ := copyEntry_cases hx
  obtain ⟨minimum', p', e', hm', hp', he', _, _, hyc⟩ := copyEntry_cases hy
  have hmin := Option.some.inj (hm'.symm.trans hm)
  have hpe := Option.some.inj (hp'.symm.trans hp)
  subst minimum'
  subst p'
  have hpn := fromRight_le_last hv.1 hv.2.2.1 (by omega : 0 < row.step + 1) hp
  rcases hxc with ⟨hxlow, hvx⟩ | ⟨hxmin, hxhigh, hvx⟩ | ⟨hxmin, hxmid, k, hk, hkv⟩
  · omega
  · rcases hyc with ⟨hylow, hvy⟩ | ⟨hymin, hyhigh, hvy⟩ | ⟨hymin, hymid, j, hj, hjv⟩
    · omega
    · omega
    · omega
  · have hvxn := copy_middle_below_owner hv hp hxmid hk hkv
    rcases hyc with ⟨hylow, hvy⟩ | ⟨hymin, hyhigh, hvy⟩ | ⟨hymin, hymid, j, hj, hjv⟩
    · omega
    · omega
    · have hij := sorted_index_lt_of_value_lt hv.1 hk hj hxy
      obtain ⟨hki, hkiv⟩ := List.getElem?_eq_some_iff.mp hkv
      obtain ⟨hji, hjiv⟩ := List.getElem?_eq_some_iff.mp hjv
      have hh := List.pairwise_iff_getElem.mp hv.1 (k + row.step) (j + row.step) hki hji (by omega)
      omega

theorem copyEntry_injective {n x y v : Nat} {row : Row}
    (hv : row.CoreValid n) (hx : copyEntry n row x = some v)
    (hy : copyEntry n row y = some v) : x = y := by
  by_cases hxy : x < y
  · have hh := copyEntry_strict hv hxy hx hy; omega
  · by_cases hyx : y < x
    · have hh := copyEntry_strict hv hyx hy hx; omega
    · omega

theorem copyEntry_order_iff {n x y vx vy : Nat} {row : Row}
    (hv : row.CoreValid n) (hx : copyEntry n row x = some vx)
    (hy : copyEntry n row y = some vy) : vx < vy ↔ x < y := by
  constructor
  · intro h
    by_cases hxy : x < y
    · exact hxy
    · by_cases he : x = y
      · subst y
        have hh := Option.some.inj (hx.symm.trans hy)
        omega
      · have hh := copyEntry_strict hv (by omega : y < x) hy hx
        omega
  · exact fun h => copyEntry_strict hv h hx hy

end FullMarkedBLP

