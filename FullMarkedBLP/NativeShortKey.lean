import FullMarkedBLP.NativeBottomGeometry
import FullMarkedBLP.CopyShortKey

namespace FullMarkedBLP

theorem nativeBlock_bottom_high_entry {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r i x : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (source : nativeSources a r = some sources)
    (nonempty : sources ≠ []) (high : row.step ≤ i) (entry : row.core[i]? = some x)
    (below : x < r) (run : nativeBlock row r sources = some block) :
    (block[0]?).bind (fun bottom =>
      bottom.core[i + (if row.core.length = 2 * row.step then 1 else 0)]?) = some x := by
  have hv := valid r row hr
  have room := Row.step_lt_length hv.2.2.2
  have eligible := nativeSources_nonempty_eligible hr source nonempty
  have step : 2 ≤ row.step := by
    by_cases one : row.step = 1
    · exact False.elim (nonempty (Option.some.inj
        (source.symm.trans (nativeSources_step_one_empty hv hr one))))
    · have := hv.2.2.2.1; omega
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) (by omega) (by omega)
  have eEntry : row.core[row.core.length - row.step]? = some e := by
    simpa [fromRight, hv.2.2.2.1, room.le] using he
  have ex : e ≤ x := by
    by_contra h
    have index := sorted_index_lt_of_value_lt hv.1 entry eEntry (by omega)
    omega
  have filter : sources.filter (· < x) = sources := by
    apply List.filter_eq_self.mpr
    intro y hy
    have bound := nativeSources_between valid hr hp he source y hy
    simp only [decide_eq_true_eq]; omega
  have rank := nativeTop_rank_exact valid hr source below.le
  rw [filter, sorted_rank_at_index hv.1 entry] at rank
  have mem := (nativeTop_core_mem row r sources x).mpr (Or.inl (List.mem_of_getElem? entry))
  have topEntry : (nativeTop row r sources).core[i + sources.length]? = some x := by
    simpa only [rank] using sorted_get_at_rank (nativeTop_sorted row r sources).1 mem
  have topValid := nativeTop_actual_coreValid valid hr source
  have topLen := nativeTop_actual_length valid hr source
  have targets : ∀ y, r ≤ y → y ≤ r + sources.length → y ∈ (nativeTop row r sources).core := by
    intro y hy hy'
    apply (nativeTop_core_mem row r sources y).mpr
    by_cases eq : y = r
    · subst y; exact Or.inl (List.mem_of_getLast? hv.2.2.1)
    · exact Or.inr (Or.inr ⟨by omega, hy'⟩)
  by_cases medium : row.core.length = 2 * row.step
  · simp only [if_pos medium]
    cases sources with
    | nil => contradiction
    | cons s ss =>
      apply nativeBlockDown_medium_bottom_high_entry ss.length topValid
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) targets
        (by change row.step + (s :: ss).length ≤ _; simp; omega)
        (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ss.length] using topEntry) below
      simpa [nativeBlock, medium] using run
  · simp only [if_neg medium, Nat.add_zero]
    have short : row.core.length + 1 = 2 * row.step := by
      have shape := hv.2.2.2
      rcases shape with ⟨_, h | h | h⟩ <;> omega
    have minStep : 3 ≤ row.step := by
      have shape := hv.2.2.2
      rcases shape with ⟨_, h | h | h⟩ <;> omega
    apply nativeBlockDown_short_bottom_high_entry sources.length topValid
      (by change _ = 2 * (row.step + sources.length); omega)
      (by change _ ≤ row.step + sources.length; omega) targets
      (by change row.step + sources.length ≤ _; omega) topEntry below
    have hbool : (row.core.length == 2 * row.step) = false := by simp [medium]
    simpa [nativeBlock, nonempty, hbool] using run

/-- The bottom row of native has exactly the input short key, including the
one-off medium-row exception. This uses no semantic realization premise. -/
theorem nativeBlock_bottom_shortKey {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (source : nativeSources a r = some sources)
    (run : nativeBlock row r sources = some block) :
    ∃ bottom, block[0]? = some bottom ∧ bottom.shortKey = row.shortKey := by
  by_cases empty : sources = []
  · subst sources
    have eq : block = [row] := (Option.some.inj run).symm
    exact ⟨row, by simp [eq], rfl⟩
  · obtain ⟨bottom, atBottom, bottomValid, stepEq, lenEq, headEq⟩ :=
      nativeBlock_bottom_geometry valid hr source empty run
    have hv := valid r row hr
    have room := Row.step_lt_length hv.2.2.2
    have dropEq : bottom.core.drop bottom.step = row.core.drop row.step := by
      apply List.ext_getElem (by simp only [List.length_drop]; omega)
      intro i hi hj
      have oldBound : row.step + i < row.core.length := by
        simp only [List.length_drop] at hj; omega
      have newBound : bottom.step + i < bottom.core.length := by
        simp only [List.length_drop] at hi; omega
      have entry : row.core[row.step + i]? = some row.core[row.step + i] := by simp [oldBound]
      have newEntry : bottom.core[bottom.step + i]? = some row.core[row.step + i] := by
        by_cases last : row.step + i = row.core.length - 1
        · have oldLast := hv.2.2.1
          have newLast := bottomValid.2.2.1
          rw [List.getLast?_eq_getElem?, ← last] at oldLast
          have ownerEq := Option.some.inj (entry.symm.trans oldLast)
          rw [ownerEq]
          have newLastIndex : bottom.step + i = bottom.core.length - 1 := by omega
          simpa only [List.getLast?_eq_getElem?, newLastIndex] using newLast
        · have below : row.core[row.step + i] < r := by
            obtain ⟨endBound, endEq⟩ := List.getElem?_eq_some_iff.mp
              (show row.core[row.core.length - 1]? = some r by
                simpa only [List.getLast?_eq_getElem?] using hv.2.2.1)
            have lt := List.pairwise_iff_getElem.mp hv.1 (row.step + i)
              (row.core.length - 1) oldBound endBound (by omega)
            simpa only [endEq] using lt
          have kept := nativeBlock_bottom_high_entry valid hr source empty (by omega) entry below run
          rw [atBottom, Option.bind_some] at kept
          have indexEq : bottom.step + i = row.step + i +
              (if row.core.length = 2 * row.step then 1 else 0) := by omega
          simpa only [indexEq] using kept
      have eq := (List.getElem?_eq_some_iff.mp newEntry).2
      simpa only [List.getElem_drop] using eq
    refine ⟨bottom, atBottom, ?_⟩
    simp only [Row.shortKey, dropEq, List.take_one, headEq]

theorem native_bottom_shortKey {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (birth : native a r = some (b, sources)) :
    ∃ bottom, rowAt b r = some bottom ∧ bottom.shortKey = row.shortKey := by
  have source := native_sources_of_success birth
  have out := birth
  unfold native at out
  rw [hr] at out
  dsimp only [Bind.bind, Option.bind] at out
  rw [source] at out
  dsimp only [Bind.bind, Option.bind] at out
  obtain ⟨block, run, out⟩ := Option.bind_eq_some_iff.mp out
  have pattern := (Prod.mk.inj (Option.some.inj out)).1
  obtain ⟨bottom, atBottom, keyEq⟩ := nativeBlock_bottom_shortKey valid hr source run
  have len := nativeBlock_length run
  have lookup := native_block_rowAt (sources := sources) hr (by omega : 0 < block.length)
  have atZero : rowAt b r = block[0]? := by
    simpa only [pattern, Nat.add_zero] using lookup
  exact ⟨bottom, atZero.trans atBottom, keyEq⟩

end FullMarkedBLP
