import FullMarkedBLP.NativeTraceClosure

namespace FullMarkedBLP

/-- Exact completion growth requires disjoint old columns, new sources and targets. -/
theorem completeMarkRow_inputs_nodup {row : Row} {y : Nat} {sources : List Nat}
    (hc : row.core.Nodup) (hs : sources.Nodup)
    (hdis : ∀ x ∈ sources, x ∉ row.core)
    (hst : ∀ x ∈ sources, x ≤ y)
    (ht : ∀ x, y < x → x ≤ y + sources.length → x ∉ row.core) :
    (row.core ++ sources ++ (List.range sources.length).map (fun i => y + 1 + i)).Nodup := by
  have hb : (row.core ++ sources).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hc, hs, ?_⟩
    intro x hx z hz he
    subst z
    exact hdis x hz hx
  have hn : (row.core ++ sources ++ (List.range sources.length).map (fun i => y + 1 + i)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hb, (after_range_sorted y sources.length).imp (fun h => Nat.ne_of_lt h), ?_⟩
    intro x hx z hz he
    subst z
    have hz' := (mem_after_range y sources.length x).mp hz
    rcases List.mem_append.mp hx with hx | hx
    · exact ht x hz'.1 hz'.2 hx
    · have hh := hst x hx; omega
  exact hn

theorem completeMarkRow_length {row : Row} {y : Nat} {sources : List Nat}
    (hc : row.core.Nodup) (hs : sources.Nodup)
    (hdis : ∀ x ∈ sources, x ∉ row.core)
    (hst : ∀ x ∈ sources, x ≤ y)
    (ht : ∀ x, y < x → x ≤ y + sources.length → x ∉ row.core) :
    (completeMarkRow row y sources).core.length = row.core.length + 2 * sources.length := by
  change (canonicalColumns _).length = _
  rw [canonicalColumns_length (completeMarkRow_inputs_nodup hc hs hdis hst ht)]
  simp only [List.length_append, List.length_map, List.length_range]
  omega
theorem completeMarkRow_shape {row : Row} {y : Nat} {sources : List Nat}
    (hv : row.OrdinaryShape)
    (hl : (completeMarkRow row y sources).core.length = row.core.length + 2 * sources.length) :
    (completeMarkRow row y sources).OrdinaryShape := by
  unfold Row.OrdinaryShape at hv ⊢
  rw [hl]
  have hs : (completeMarkRow row y sources).step = row.step + sources.length := rfl
  rw [hs]
  rcases hv with ⟨hp, h | h | h⟩ <;> omega

theorem completeMarkRow_coreValid {row : Row} {owner y : Nat} {sources : List Nat}
    (hv : row.CoreValid owner)
    (hs : sources.Nodup) (hdis : ∀ x ∈ sources, x ∉ row.core)
    (hst : ∀ x ∈ sources, x ≤ y)
    (ht : ∀ x, y < x → x ≤ y + sources.length → x ∉ row.core)
    (hy : y + sources.length ≤ owner) :
    (completeMarkRow row y sources).CoreValid owner := by
  have hl := completeMarkRow_length (hv.1.imp (fun h => Nat.ne_of_lt h)) hs hdis hst ht
  have hmin := hv.2.1
  refine ⟨(completeMarkRow_sorted row y sources).1, by omega, ?_, completeMarkRow_shape hv.2.2.2 hl⟩
  apply sorted_last_of_max (completeMarkRow_sorted row y sources).1
  · exact (completeMarkRow_core_mem row y sources owner).mpr (Or.inl (List.mem_of_getLast? hv.2.2.1))
  · intro x hx
    rcases (completeMarkRow_core_mem row y sources x).mp hx with hx | hx | hx
    · exact core_entry_le_owner hv hx
    · have hh := hst x hx; omega
    · omega

end FullMarkedBLP


