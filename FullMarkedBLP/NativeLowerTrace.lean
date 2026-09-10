import FullMarkedBLP.NativeOldMark

namespace FullMarkedBLP

/-- Deleting an existing smaller entry moves a later entry exactly one place. -/
theorem erase_smaller_preserves_index {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {k y removed : Nat} (hy : xs[k]? = some y) (hm : removed ∈ xs) (hlt : removed < y) :
    (xs.erase removed)[k - 1]? = some y := by
  induction xs generalizing k with
  | nil => simp at hm
  | cons z zs ih =>
    cases k with
    | zero =>
      have he : z = y := by simpa using hy
      subst z
      rcases List.mem_cons.mp hm with he | hm
      · omega
      · have hh := (List.pairwise_cons.mp hs).1 removed hm
        omega
    | succ k =>
      have hy' : zs[k]? = some y := by simpa using hy
      by_cases hz : z = removed
      · subst z; simpa using hy'
      · have hm' : removed ∈ zs := (List.mem_cons.mp hm).resolve_left (Ne.symm hz)
        have hk : 0 < k := by
          cases k with
          | zero =>
            have he : zs.head? = some y := by simpa [List.head?_eq_getElem?] using hy'
            obtain ⟨tail, heq⟩ := List.head?_eq_some_iff.mp he
            subst zs
            rcases List.mem_cons.mp hm' with he | hm'
            · omega
            · have hh := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 removed hm'
              omega
          | succ k => omega
        have ht := ih (List.pairwise_cons.mp hs).2 hy' hm'
        simp only [List.erase_cons, beq_iff_eq, hz, ↓reduceIte, Nat.add_sub_cancel]
        rw [show k = (k - 1) + 1 by omega, List.getElem?_cons_succ]
        exact ht

/-- In the medium exception, both ends of a retained step-pair keep their indices. -/
theorem nativeLower_medium_pair {row lower : Row} {owner k y x : Nat}
    (hv : row.CoreValid owner) (hy : y < owner)
    (hky : row.core[k]? = some y) (hkx : row.core[k - row.step]? = some x)
    (h : nativeLower row owner true = some lower) :
    lower.core[k]? = some y ∧ lower.core[k - lower.step]? = some x := by
  have hi : k - row.step < row.core.length - row.step := by
    have hk := (List.getElem?_eq_some_iff.mp hky).1
    have hl := Row.step_lt_length hv.2.2.2
    omega
  have hs := nativeLower_keeps_low_entry hv hi hkx h
  cases Option.some.inj h
  exact ⟨erase_greater_preserves_index hv.1 hky hy, hs⟩

theorem nativeLower_short_pair {row lower : Row} {owner k y x : Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner)
    (hlen : row.core.length + 1 = 2 * row.step)
    (hy : y ∈ row.marks) (hk : row.step ≤ k)
    (hky : row.core[k]? = some y) (hkx : row.core[k - row.step]? = some x)
    (h : nativeLower row owner false = some lower) :
    lower.core[k - 1]? = some y ∧
      lower.core[k - 1 - lower.step]? = some x := by
  have hi : k - row.step < row.core.length - row.step := by
    have hkb := (List.getElem?_eq_some_iff.mp hky).1
    have hl := Row.step_lt_length hv.2.2.2
    omega
  have hs := nativeLower_keeps_low_entry hv hi hkx h
  obtain ⟨source, he, hout⟩ := Option.bind_eq_some_iff.mp h
  have hstep : 1 < row.step := by
    have hl := hv.2.1
    omega
  have hso := fromRight_lt_last hv.1 hv.2.2.1 hstep he
  have hsm : source ∈ row.core := by
    unfold Row.e fromRight at he
    split at he
    next => exact List.mem_iff_getElem?.mpr ⟨_, he⟩
    next => simp at he
  have hsm' : source ∈ row.core.erase owner :=
    (List.mem_erase_of_ne (Nat.ne_of_lt hso)).mpr hsm
  have hsy := short_source_before_mark hv hm hlen he hy
  have htarget := erase_greater_preserves_index hv.1 hky (hm.2 y hy).1
  have htarget' := erase_smaller_preserves_index (hv.1.sublist List.erase_sublist) htarget hsm' hsy
  cases Option.some.inj hout
  refine ⟨htarget', ?_⟩
  have heq : k - 1 - (row.step - 1) = k - row.step := by omega
  simpa only [heq] using hs

end FullMarkedBLP



