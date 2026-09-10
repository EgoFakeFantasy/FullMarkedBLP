import FullMarkedBLP.NativeLower

namespace FullMarkedBLP

/-- Consecutive final integer columns must occupy consecutive list positions. -/
theorem penultimate_index {row : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : owner - 1 ∈ row.core) (ho : 0 < owner) :
    row.core[row.core.length - 2]? = some (owner - 1) := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  have hl := hv.2.2.1
  rw [List.getLast?_eq_getElem?] at hl
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hl
  have hij : i < row.core.length - 1 := by
    by_cases hh : i = row.core.length - 1
    · subst i; omega
    · omega
  have heq : i = row.core.length - 2 := by
    by_cases hh : i + 1 < row.core.length - 1
    · have hb := List.pairwise_iff_getElem.mp hv.1 i (i + 1) hi (by omega) (by omega)
      have hc := List.pairwise_iff_getElem.mp hv.1 (i + 1) (row.core.length - 1)
        (by omega) hj hh
      rw [he] at hb
      rw [hjv] at hc
      omega
    · omega
  apply List.getElem?_eq_some_iff.mpr
  subst i
  exact ⟨hi, he⟩

/-- Step at least three puts e strictly left of the preceding integer column. -/
theorem source_below_previous_owner {row : Row} {owner source : Nat}
    (hv : row.CoreValid owner) (hm : owner - 1 ∈ row.core) (ho : 0 < owner)
    (hstep : 2 < row.step) (he : row.e = some source) : source < owner - 1 := by
  have hp := penultimate_index hv hm ho
  obtain ⟨hi, hpi⟩ := List.getElem?_eq_some_iff.mp hp
  unfold Row.e fromRight at he
  split at he
  next hb =>
    obtain ⟨hj, hej⟩ := List.getElem?_eq_some_iff.mp he
    have hh := List.pairwise_iff_getElem.mp hv.1 (row.core.length - row.step)
      (row.core.length - 2) hj hi (by omega)
    simpa [hej, hpi] using hh
  next => simp at he

/-- Full single-step core validity with the source gap derived from indices. -/
theorem nativeLower_short_coreValid {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : owner - 1 ∈ row.core) (ho : 0 < owner)
    (hstep : 3 < row.step) (hlen : row.core.length + 1 = 2 * row.step)
    (h : nativeLower row owner false = some lower) : lower.CoreValid (owner - 1) := by
  have hs := nativeLower_short_shape hv hstep hlen h
  have hl := nativeLower_length hv (by omega) h
  obtain ⟨source, he⟩ := fromRight_exists (xs := row.core) hv.2.2.2.1
    (Nat.le_of_lt (Row.step_lt_length hv.2.2.2))
  refine ⟨nativeLower_sorted hv.1 h, ?_, ?_, hs.1⟩
  · omega
  · exact nativeLower_endpoint hv hm he
      (source_below_previous_owner hv hm ho (by omega) he) h

#print axioms nativeLower_short_coreValid



theorem sorted_index_spacing {xs : List Nat} (hs : xs.Pairwise (· < ·))
    (i d : Nat) (hi : i < xs.length) (hd : i + d < xs.length) :
    xs[i] + d ≤ xs[i + d] := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hp : i + d < xs.length := by omega
    have hh := ih hp
    have hn := List.pairwise_iff_getElem.mp hs (i + d) (i + (d + 1)) hp hd (by omega)
    omega

/-- Numeric spacing of increasing natural columns bounds the e-source. -/
theorem source_spacing {row : Row} {owner source : Nat}
    (hv : row.CoreValid owner) (he : row.e = some source) :
    source + (row.step - 1) ≤ owner := by
  have hl := hv.2.2.1
  rw [List.getLast?_eq_getElem?] at hl
  obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hl
  unfold Row.e fromRight at he
  split at he
  next hb =>
    obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp he
    have hidx : row.core.length - row.step + (row.step - 1) = row.core.length - 1 := by omega
    have hh := sorted_index_spacing hv.1 (row.core.length - row.step) (row.step - 1)
      hi (by omega)
    simpa only [hidx, hiv, hjv] using hh
  next => simp at he

/-- The complete consecutive target segment is kept at every short descent. -/
theorem nativeLower_preserves_targets {row lower : Row} {base k : Nat}
    (hv : row.CoreValid (base + k))
    (htarget : ∀ x, base ≤ x → x ≤ base + k → x ∈ row.core)
    (hstep : k + 2 ≤ row.step)
    (h : nativeLower row (base + k) false = some lower) :
    ∀ x, base ≤ x → x < base + k → x ∈ lower.core := by
  obtain ⟨source, he, hout⟩ := Option.bind_eq_some_iff.mp h
  have hb := source_spacing hv he
  cases Option.some.inj hout
  intro x hx hx'
  apply (List.mem_erase_of_ne (by omega)).mpr
  exact (List.mem_erase_of_ne (by omega)).mpr (htarget x hx (by omega))

#print axioms source_spacing
end FullMarkedBLP

