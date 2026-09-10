import FullMarkedBLP.NativeCounting

namespace FullMarkedBLP

theorem nativeLower_core_sublist {row lower : Row} {owner : Nat} {medium : Bool}
    (h : nativeLower row owner medium = some lower) : List.Sublist lower.core row.core := by
  unfold nativeLower at h
  split at h
  next => cases Option.some.inj h; exact List.erase_sublist
  next =>
    obtain ⟨source, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    exact List.erase_sublist.trans List.erase_sublist

theorem nativeLower_sorted {row lower : Row} {owner : Nat} {medium : Bool}
    (hs : row.core.Pairwise (· < ·))
    (h : nativeLower row owner medium = some lower) : lower.core.Pairwise (· < ·) :=
  hs.sublist (nativeLower_core_sublist h)

theorem nativeLower_exists {row : Row} {owner : Nat} (medium : Bool)
    (hs : row.OrdinaryShape) : ∃ lower, nativeLower row owner medium = some lower := by
  cases medium with
  | true => exact ⟨_, rfl⟩
  | false =>
    obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) hs.1
      (Nat.le_of_lt (Row.step_lt_length hs))
    exact ⟨⟨(row.core.erase owner).erase e, row.step - 1, row.marks.erase (owner - 1)⟩,
      by simp [nativeLower, Row.e, he]⟩

theorem nativeLower_step {row lower : Row} {owner : Nat} {medium : Bool}
    (h : nativeLower row owner medium = some lower) :
    lower.step = if medium then row.step else row.step - 1 := by
  unfold nativeLower at h
  split at h
  next => cases Option.some.inj h; simp_all
  next =>
    obtain ⟨source, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    simp_all

theorem nativeLower_length {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hstep : 1 < row.step)
    (h : nativeLower row owner false = some lower) :
    lower.core.length = row.core.length - 2 := by
  obtain ⟨source, he, h⟩ := Option.bind_eq_some_iff.mp h
  have hlt := fromRight_lt_last hv.1 hv.2.2.1 hstep he
  have hm : owner ∈ row.core := List.mem_of_getLast? hv.2.2.1
  have hs : source ∈ row.core := by
    unfold Row.e fromRight at he
    split at he
    next => exact List.mem_iff_getElem?.mpr ⟨_, he⟩
    next => simp at he
  have hs' : source ∈ row.core.erase owner :=
    (List.mem_erase_of_ne (Nat.ne_of_lt hlt)).mpr hs
  cases Option.some.inj h
  simp only [List.length_erase_of_mem hs', List.length_erase_of_mem hm]
  omega

theorem nativeLower_short_shape {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hstep : 3 < row.step)
    (hlen : row.core.length + 1 = 2 * row.step)
    (h : nativeLower row owner false = some lower) :
    lower.OrdinaryShape ∧ lower.core.length + 1 = 2 * lower.step := by
  have hl := nativeLower_length hv (by omega) h
  have hs := nativeLower_step h
  simp only [Bool.false_eq_true, ↓reduceIte] at hs
  unfold Row.OrdinaryShape
  rw [hs, hl]
  omega

theorem nativeLower_medium_shape {row lower : Row} {owner : Nat}
    (hm : owner ∈ row.core) (hstep : 3 ≤ row.step)
    (hlen : row.core.length = 2 * row.step)
    (h : nativeLower row owner true = some lower) :
    lower.OrdinaryShape ∧ lower.core.length + 1 = 2 * lower.step := by
  cases Option.some.inj h
  simp only [Row.OrdinaryShape, List.length_erase_of_mem hm]
  omega

#print axioms nativeLower_short_shape
#print axioms nativeLower_medium_shape






theorem sorted_last_of_max {xs : List Nat} {m : Nat}
    (hs : xs.Pairwise (· < ·)) (hm : m ∈ xs) (hb : ∀ x ∈ xs, x ≤ m) :
    xs.getLast? = some m := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    cases xs with
    | nil => simp at hm; subst m; rfl
    | cons y ys =>
      have ht : m ∈ y :: ys := by
        rcases List.mem_cons.mp hm with he | ht
        · have hh := (List.pairwise_cons.mp hs).1 y (by simp)
          have hh' := hb y (by simp)
          omega
        · exact ht
      have hh := ih (List.pairwise_cons.mp hs).2 ht
        (fun z hz => hb z (List.mem_cons_of_mem x hz))
      exact hh

/-- Endpoint after deleting the owner, provided the preceding integer remains. -/
theorem erase_owner_last {row : Row} {owner : Nat}
    (hv : row.CoreValid owner) (hm : owner - 1 ∈ row.core) (ho : 0 < owner) :
    (row.core.erase owner).getLast? = some (owner - 1) := by
  have hn : row.core.Nodup := hv.1.imp (fun h => Nat.ne_of_lt h)
  apply sorted_last_of_max (hv.1.sublist List.erase_sublist)
  · exact (List.mem_erase_of_ne (by omega)).mpr hm
  · intro x hx
    have hh := hn.mem_erase_iff.mp hx
    have hb := core_entry_le_owner hv hh.2
    omega

theorem nativeLower_endpoint {row lower : Row} {owner source : Nat}
    (hv : row.CoreValid owner) (hm : owner - 1 ∈ row.core)
    (he : row.e = some source) (hsource : source < owner - 1)
    (h : nativeLower row owner false = some lower) :
    lower.core.getLast? = some (owner - 1) := by
  have ho : 0 < owner := by omega
  have hn : row.core.Nodup := hv.1.imp (fun h => Nat.ne_of_lt h)
  have hout : lower = ⟨(row.core.erase owner).erase source, row.step - 1,
      row.marks.erase (owner - 1)⟩ := by
    simpa [nativeLower, he] using h.symm
  rw [hout]
  apply sorted_last_of_max
  · exact hv.1.sublist (List.erase_sublist.trans List.erase_sublist)
  · apply (List.mem_erase_of_ne (Nat.ne_of_gt hsource)).mpr
    exact (List.mem_erase_of_ne (by omega)).mpr hm
  · intro x hx
    have hx' := List.mem_of_mem_erase hx
    have hh := hn.mem_erase_iff.mp hx'
    have hb := core_entry_le_owner hv hh.2
    omega

#print axioms nativeLower_endpoint



/-- The actual native top has the correct endpoint as well as ordinary shape. -/
theorem nativeTop_actual_coreValid {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources) :
    (nativeTop row r sources).CoreValid (r + sources.length) := by
  have hv := valid r row hr
  refine ⟨(nativeTop_sorted row r sources).1, ?_, ?_, nativeTop_actual_shape valid hr h⟩
  · rw [nativeTop_actual_length valid hr h]
    have := hv.2.1
    omega
  · apply sorted_last_of_max (nativeTop_sorted row r sources).1
    · apply (nativeTop_core_mem row r sources _).mpr
      by_cases hz : sources.length = 0
      · left
        simpa [hz] using List.mem_of_getLast? hv.2.2.1
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · intro x hx
      rcases (nativeTop_core_mem row r sources x).mp hx with hx | hx | hx
      · have := core_entry_le_owner hv hx; omega
      · have := nativeSources_below_owner valid hr h x hx; omega
      · exact hx.2

#print axioms nativeTop_actual_coreValid
end FullMarkedBLP
