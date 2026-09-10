import FullMarkedBLP.TraceTransport

namespace FullMarkedBLP

theorem nativeLower_keeps_low_entry {row lower : Row} {owner i x : Nat} {medium : Bool}
    (hv : row.CoreValid owner) (hi : i < row.core.length - row.step)
    (hx : row.core[i]? = some x) (h : nativeLower row owner medium = some lower) :
    lower.core[i]? = some x := by
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) hv.2.2.2.1
    (Nat.le_of_lt (Row.step_lt_length hv.2.2.2))
  have hei := he
  unfold fromRight at hei
  split at hei
  next hb =>
    obtain ⟨hj, hje⟩ := List.getElem?_eq_some_iff.mp hei
    obtain ⟨hix, hixv⟩ := List.getElem?_eq_some_iff.mp hx
    have hxe := List.pairwise_iff_getElem.mp hv.1 i (row.core.length - row.step) hix hj hi
    rw [hixv, hje] at hxe
    have heo := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
    have hfirst := erase_greater_preserves_index hv.1 hx (by omega : x < owner)
    cases medium with
    | true => cases Option.some.inj h; exact hfirst
    | false =>
      have hout : lower = ⟨(row.core.erase owner).erase e, row.step - 1,
          row.marks.erase (owner - 1)⟩ := by simpa [nativeLower, Row.e, he] using h.symm
      rw [hout]
      exact erase_greater_preserves_index (hv.1.sublist List.erase_sublist) hfirst hxe
  next => simp at hei

/-- Both descent cases move the p-source one old core position to the left. -/
theorem nativeLower_p {row lower : Row} {owner p : Nat} {medium : Bool}
    (hv : row.CoreValid owner) (hstep : 1 < row.step)
    (hroom : row.step + 2 ≤ row.core.length)
    (hp : fromRight row.core (row.step + 2) = some p)
    (h : nativeLower row owner medium = some lower) : lower.p = some p := by
  have hpi : row.core[row.core.length - (row.step + 2)]? = some p := by
    simpa [fromRight, hroom] using hp
  have hread := nativeLower_keeps_low_entry hv (by omega) hpi h
  have hs := nativeLower_step h
  have hm : owner ∈ row.core := List.mem_of_getLast? hv.2.2.1
  cases medium with
  | false =>
    have hl := nativeLower_length hv hstep h
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have hpos : 0 < lower.step + 1 := by omega
    have hb : lower.step + 1 ≤ lower.core.length := by omega
    have hi : lower.core.length - (lower.step + 1) = row.core.length - (row.step + 2) := by omega
    simpa [Row.p, fromRight, hpos, hb, hi] using hread
  | true =>
    have hl : lower.core.length = row.core.length - 1 := by
      cases Option.some.inj h
      exact List.length_erase_of_mem hm
    simp only [↓reduceIte] at hs
    have hb : lower.step + 1 ≤ lower.core.length := by omega
    have hi : lower.core.length - (lower.step + 1) = row.core.length - (row.step + 2) := by omega
    simpa [Row.p, fromRight, hb, hi] using hread


theorem nativeLower_keeps_low_index {row lower : Row} {owner i : Nat} {medium : Bool}
    (hv : row.CoreValid owner) (hi : i < row.core.length - row.step)
    (h : nativeLower row owner medium = some lower) :
    lower.core[i]? = row.core[i]? := by
  have hib : i < row.core.length := by omega
  have he : row.core[i]? = some row.core[i] := by simp [hib]
  exact (nativeLower_keeps_low_entry hv hi he h).trans he.symm

/-- P-values of the short block are consecutive entries of its top core. -/
theorem nativeBlockDown_short_p (k : Nat) {base startIndex : Nat} {top : Row} {block : Pattern}
    (hv : top.CoreValid (base + k))
    (hlen : top.core.length + 1 = 2 * top.step) (hstep : k + 3 ≤ top.step)
    (hindex : top.core.length = startIndex + k + top.step + 1)
    (htarget : ∀ x, base ≤ x → x ≤ base + k → x ∈ top.core)
    (h : nativeBlockDown k (base + k) false top = some block) :
    ∀ j (hj : j < block.length), (block[j]).p = top.core[startIndex + j]? := by
  induction k generalizing top block with
  | zero =>
    cases Option.some.inj h
    intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    have hi : top.core.length - (top.step + 1) = startIndex := by omega
    simp [Row.p, fromRight, hi, show top.step + 1 ≤ top.core.length by omega]
  | succ k ih =>
    obtain ⟨lower, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨earlier, he, h⟩ := Option.bind_eq_some_iff.mp h
    change some (earlier ++ [top]) = some block at h
    cases Option.some.inj h
    have hprev : base + (k + 1) - 1 = base + k := by omega
    have hm : base + (k + 1) - 1 ∈ top.core := htarget _ (by omega) (by omega)
    have hv' := nativeLower_short_coreValid hv hm (by omega) (by omega) hlen hl
    rw [hprev] at hv' he
    have hs' := (nativeLower_short_shape hv (by omega) hlen hl).2
    have hlen' := nativeLower_length hv (by omega) hl
    have hstep' := nativeLower_step hl
    simp only [Bool.false_eq_true, ↓reduceIte] at hstep'
    have ht' := nativeLower_preserves_targets hv htarget (by omega) hl
    have hi' : lower.core.length = startIndex + k + lower.step + 1 := by omega
    have hh := ih hv' hs' (by omega) hi' (fun x hx hb => ht' x hx (by omega)) he
    have heLen := nativeBlockDown_length he
    intro j hj
    by_cases hjl : j < earlier.length
    · rw [List.getElem_append_left hjl, hh j hjl]
      exact nativeLower_keeps_low_index hv (by omega) hl
    · have hjeq : j = earlier.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      subst j
      have hi : top.core.length - (top.step + 1) = startIndex + (k + 1) := by omega
      simp [heLen, Row.p, fromRight, hi, show top.step + 1 ≤ top.core.length by omega]


theorem nativeBlockDown_medium_p (k : Nat) {base startIndex : Nat} {top : Row} {block : Pattern}
    (hv : top.CoreValid (base + (k + 1)))
    (hlen : top.core.length = 2 * top.step) (hstep : k + 3 ≤ top.step)
    (hindex : top.core.length = startIndex + (k + 1) + top.step + 1)
    (htarget : ∀ x, base ≤ x → x ≤ base + (k + 1) → x ∈ top.core)
    (h : nativeBlockDown (k + 1) (base + (k + 1)) true top = some block) :
    ∀ j (hj : j < block.length), (block[j]).p = top.core[startIndex + j]? := by
  let lower : Row := ⟨top.core.erase (base + (k + 1)), top.step,
    top.marks.erase (base + (k + 1) - 1)⟩
  have hl : nativeLower top (base + (k + 1)) true = some lower := rfl
  obtain ⟨earlier, he, h⟩ := Option.bind_eq_some_iff.mp h
  change some (earlier ++ [top]) = some block at h
  cases Option.some.inj h
  have ho : base + (k + 1) ∈ top.core := List.mem_of_getLast? hv.2.2.1
  have hs := nativeLower_medium_shape ho (by omega) hlen hl
  have hprev : base + (k + 1) - 1 = base + k := by omega
  have hm : base + (k + 1) - 1 ∈ top.core := htarget _ (by omega) (by omega)
  have hout : lower = ⟨top.core.erase (base + (k + 1)), top.step,
      top.marks.erase (base + (k + 1) - 1)⟩ := (Option.some.inj hl).symm
  have hlen' : lower.core.length = top.core.length - 1 := by
    rw [hout]; exact List.length_erase_of_mem ho
  have hstep' : lower.step = top.step := by rw [hout]
  have hv' : lower.CoreValid (base + k) := by
    refine ⟨nativeLower_sorted hv.1 hl, by omega, ?_, hs.1⟩
    rw [hout]
    simpa [hprev] using erase_owner_last hv hm (by omega)
  have ht' : ∀ x, base ≤ x → x ≤ base + k → x ∈ lower.core := by
    intro x hx hb
    rw [hout]
    exact (List.mem_erase_of_ne (by omega)).mpr (htarget x hx (by omega))
  rw [hprev] at he
  have hi' : lower.core.length = startIndex + k + lower.step + 1 := by omega
  have hh := nativeBlockDown_short_p k hv' hs.2 (by omega) hi' ht' he
  have heLen := nativeBlockDown_length he
  intro j hj
  by_cases hjl : j < earlier.length
  · rw [List.getElem_append_left hjl, hh j hjl]
    exact nativeLower_keeps_low_index hv (by omega) hl
  · have hjeq : j = earlier.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    have hi : top.core.length - (top.step + 1) = startIndex + (k + 1) := by omega
    simp [heLen, Row.p, fromRight, hi, show top.step + 1 ≤ top.core.length by omega]

end FullMarkedBLP
