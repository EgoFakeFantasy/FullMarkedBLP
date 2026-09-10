import FullMarkedBLP.RankWordMinimum

namespace FullMarkedBLP

theorem row_p_minimum_shape {row : Row} {owner minimum : Nat}
    (hv : row.CoreValid owner) (hm : row.core.head? = some minimum)
    (hp : row.p = some minimum) : row.core = [minimum, owner] ∧ row.step = 1 := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hpos := hv.2.2.2.1
  have hpi : row.core[row.core.length - (row.step + 1)]? = some minimum := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hmi : row.core[0]? = some minimum := by simpa [List.head?_eq_getElem?] using hm
  obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp hpi
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hmi
  have hidx : row.core.length - (row.step + 1) = 0 := by
    by_contra hn
    have hh := List.pairwise_iff_getElem.mp hv.1 0 _ hj hi (by omega)
    rw [hiv, hjv] at hh
    omega
  have hs := hv.2.2.2
  have hshape : row.core.length = 2 ∧ row.step = 1 := by
    rcases hs with ⟨_, hs | hs | hs⟩ <;> omega
  refine ⟨?_, hshape.2⟩
  have hl := hv.2.2.1
  cases he : row.core with
  | nil => simp [he] at hshape
  | cons x tail =>
    cases tail with
    | nil => simp [he] at hshape
    | cons y rest =>
      have hrnil : rest = [] := by simpa [he] using hshape.1
      subst rest
      have hx : x = minimum := by simpa [he] using hm
      have hy : y = owner := by simpa [he] using hl
      simp [hx, hy]

theorem native_empty_of_p_minimum {a : Pattern} {row : Row} {owner minimum : Nat}
    (hr : rowAt a owner = some row) (hv : row.CoreValid owner)
    (hm : row.core.head? = some minimum) (hp : row.p = some minimum) :
    native a owner = some (a, []) := by
  obtain ⟨hcore, hstep⟩ := row_p_minimum_shape hv hm hp
  apply native_empty hr
  simp [nativeSources, hr, hcore, hstep, Row.p, Row.e, Row.b, fromRight, nativeSourcesFuel]

theorem native_nonempty_minimum_lt_p {a b : Pattern} {row : Row} {owner minimum p : Nat}
    {sources : List Nat} (hr : rowAt a owner = some row) (hv : row.CoreValid owner)
    (hm : row.core.head? = some minimum) (hp : row.p = some p)
    (hn : native a owner = some (b, sources)) (hne : sources ≠ []) : minimum < p := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hle := core_head_le_entry hv hm hpi
  by_contra hh
  have he : p = minimum := by omega
  have hempty := native_empty_of_p_minimum hr hv hm (by simpa [he] using hp)
  have hs := (Prod.mk.inj (Option.some.inj (hn.symm.trans hempty))).2
  exact hne hs

end FullMarkedBLP

