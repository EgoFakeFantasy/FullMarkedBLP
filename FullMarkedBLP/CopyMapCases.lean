import FullMarkedBLP.PacketChains

namespace FullMarkedBLP

/-- The middle branch is an exact step-offset pair in the last core. -/
theorem copy_pair_lookup {row : Row} {x v : Nat}
    (h : ((row.core.zip (row.core.drop row.step)).find? (fun pair => pair.1 == x)).map Prod.snd = some v) :
    ∃ k, row.core[k]? = some x ∧ row.core[k + row.step]? = some v := by
  obtain ⟨pair, hp, hv⟩ := Option.map_eq_some_iff.mp h
  have hx : pair.1 = x := by simpa using List.find?_some hp
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hp)
  have hkl : k < row.core.length := by simp at hk; omega
  have hkr : k < (row.core.drop row.step).length := by simp only [List.length_drop]; simp at hk; omega
  have hleft := congrArg Prod.fst he
  have hright := congrArg Prod.snd he
  simp only [List.getElem_zip] at hleft hright
  refine ⟨k, ?_, ?_⟩
  · exact List.getElem?_eq_some_iff.mpr ⟨hkl, hleft.trans hx⟩
  · have heq : row.step + k = k + row.step := by omega
    have hh : (row.core.drop row.step)[k]? = some v :=
      List.getElem?_eq_some_iff.mpr ⟨hkr, hright.trans hv⟩
    simpa [heq] using hh

theorem copyEntry_cases {n x v : Nat} {row : Row} (h : copyEntry n row x = some v) :
    ∃ minimum p e, row.core.head? = some minimum ∧ row.p = some p ∧ row.e = some e ∧
      p ≠ 0 ∧ x ≤ e ∧
      ((x < minimum ∧ v = x) ∨
       (minimum ≤ x ∧ p ≤ x ∧ v = x + (n - p)) ∨
       (minimum ≤ x ∧ x < p ∧ ∃ k, row.core[k]? = some x ∧ row.core[k + row.step]? = some v)) := by
  obtain ⟨minimum, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next => simp at h
  next hn =>
    split at h
    next => simp at h
    next hb =>
      refine ⟨minimum, p, e, hm, hp, he, hn, by omega, ?_⟩
      split at h
      next hlow => exact Or.inl ⟨hlow, (Option.some.inj h).symm⟩
      next hlow =>
        split at h
        next hhigh => exact Or.inr (Or.inl ⟨by omega, hhigh, (Option.some.inj h).symm⟩)
        next hhigh =>
          obtain ⟨pair, hpair, hout⟩ := Option.bind_eq_some_iff.mp h
          have hmapped : ((row.core.zip (row.core.drop row.step)).find? (fun pair => pair.1 == x)).map Prod.snd = some v := by
            simpa only [hpair, Option.map_some] using hout
          exact Or.inr (Or.inr ⟨by omega, by omega, copy_pair_lookup hmapped⟩)

theorem copyEntry_not_below_input {n x v : Nat} {row : Row}
    (hv : row.CoreValid n) (h : copyEntry n row x = some v) : x ≤ v := by
  obtain ⟨minimum, p, e, _, _, _, _, _, hcases⟩ := copyEntry_cases h
  rcases hcases with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨_, _, k, hx, hv'⟩
  · omega
  · omega
  · obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hj, he'⟩ := List.getElem?_eq_some_iff.mp hv'
    have hstep := hv.2.2.2.1
    have hh := List.pairwise_iff_getElem.mp hv.1 k (k + row.step) hi hj (by omega)
    omega

end FullMarkedBLP


