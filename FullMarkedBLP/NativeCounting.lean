import FullMarkedBLP.NativeSources

namespace FullMarkedBLP

theorem insertColumn_length_of_not_mem (x : Nat) {xs : List Nat} (hx : x ∉ xs) :
    (insertColumn x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hne : x ≠ y := by intro he; subst x; simp at hx
    have ht : x ∉ ys := by intro h; exact hx (List.mem_cons_of_mem y h)
    simp only [insertColumn]
    split
    · simp
    · simp [ih ht]

theorem canonicalColumns_length {xs : List Nat} (h : xs.Nodup) :
    (canonicalColumns xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp h
    change (insertColumn x (canonicalColumns xs)).length = (x :: xs).length
    rw [insertColumn_length_of_not_mem x (by simpa [mem_canonicalColumns] using hx), ih ht]
    rfl

theorem after_range_sorted (r t : Nat) :
    ((List.range t).map (fun i => r + 1 + i)).Pairwise (· < ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simpa using Nat.add_lt_add_left hij (r + 1)

/-- Exact counting needs disjointness; sorting alone would not justify 2t. -/
theorem nativeTop_length {row : Row} {r : Nat} {sources : List Nat}
    (hc : row.core.Nodup) (hs : sources.Nodup)
    (hdis : ∀ x ∈ sources, x ∉ row.core)
    (hcb : ∀ x ∈ row.core, x ≤ r) (hsb : ∀ x ∈ sources, x ≤ r) :
    (nativeTop row r sources).core.length = row.core.length + 2 * sources.length := by
  have hbase : (row.core ++ sources).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hc, hs, ?_⟩
    intro x hx y hy he
    subst y
    exact hdis x hy hx
  have ht : ((List.range sources.length).map (fun i => r + 1 + i)).Nodup :=
    (after_range_sorted r sources.length).imp (fun hh => Nat.ne_of_lt hh)
  have hall : (row.core ++ sources ++
      (List.range sources.length).map (fun i => r + 1 + i)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hbase, ht, ?_⟩
    intro x hx y hy he
    have hb := (mem_after_range r sources.length y).mp hy
    have hxle : x ≤ r := by
      rcases List.mem_append.mp hx with hx | hx
      · exact hcb x hx
      · exact hsb x hx
    omega
  change (canonicalColumns _).length = _
  rw [canonicalColumns_length hall]
  simp only [List.length_append, List.length_map, List.length_range]
  omega


theorem core_entry_le_owner {row : Row} {r x : Nat}
    (hv : row.CoreValid r) (hx : x ∈ row.core) : x ≤ r := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  have hk : 0 < row.core.length - i := by omega
  have hb : row.core.length - i ≤ row.core.length := by omega
  have hh : fromRight row.core (row.core.length - i) = some x := by
    simp [fromRight, hk, hb, Nat.sub_sub_self (Nat.le_of_lt hi), hi, he]
  exact fromRight_le_last hv.1 hv.2.2.1 hk hh

theorem nativeSources_below_owner {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources) :
    ∀ x ∈ sources, x < r := by
  unfold nativeSources at h
  rw [hr] at h
  dsimp only [Bind.bind, Option.bind] at h
  split at h
  next =>
    change some [] = some sources at h
    cases Option.some.inj h
    simp
  next =>
    obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
    have hv := valid r row hr
    have hb := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
    intro x hx
    have hh := nativeSourcesFuel_bounds valid h x hx
    omega

theorem nativeTop_actual_length {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources) :
    (nativeTop row r sources).core.length = row.core.length + 2 * sources.length := by
  apply nativeTop_length
  · exact (valid r row hr).1.imp (fun hh => Nat.ne_of_lt hh)
  · exact (nativeSources_decreasing valid h).imp (fun hh => Nat.ne_of_gt hh)
  · exact nativeSources_disjoint valid hr h
  · exact fun x hx => core_entry_le_owner (valid r row hr) hx
  · exact fun x hx => Nat.le_of_lt (nativeSources_below_owner valid hr h x hx)

theorem nativeTop_actual_shape {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources) :
    (nativeTop row r sources).OrdinaryShape := by
  have hl := nativeTop_actual_length valid hr h
  have hs := (valid r row hr).2.2.2
  unfold Row.OrdinaryShape at hs ⊢
  rw [hl]
  change 0 < row.step + sources.length ∧ _
  have hstep : (nativeTop row r sources).step = row.step + sources.length := rfl
  rw [hstep]
  rcases hs with ⟨hp, h | h | h⟩ <;> omega

end FullMarkedBLP
