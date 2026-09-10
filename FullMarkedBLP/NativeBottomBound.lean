import FullMarkedBLP.NativeSuffixSat

namespace FullMarkedBLP

theorem core_entry_le_b {row : Row} {owner x v : Nat}
    (hv : row.CoreValid owner) (hb : row.b = some v)
    (hx : x ∈ row.core) (hxo : x < owner) : x ≤ v := by
  have hlen := hv.2.1
  have hb' : row.core[row.core.length - 2]? = some v := by
    simpa [Row.b, fromRight, show 2 ≤ row.core.length by omega] using hb
  have ho : row.core[row.core.length - 1]? = some owner := by
    simpa [List.getLast?_eq_getElem?] using hv.2.2.1
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have hio := sorted_index_lt_of_value_lt hv.1 hi ho hxo
  by_cases hle : x ≤ v
  · exact hle
  · have hvi := sorted_index_lt_of_value_lt hv.1 hb' hi (by omega : v < x)
    omega

theorem nativeBlockDown_core_subset {k owner : Nat} {medium : Bool} {top out : Row} {block : Pattern}
    (h : nativeBlockDown k owner medium top = some block) (hm : out ∈ block) :
    ∀ x ∈ out.core, x ∈ top.core := by
  induction k generalizing owner medium top block with
  | zero =>
    have he : block = [top] := by simpa [nativeBlockDown] using h.symm
    have he' : out = top := by simpa [he] using hm
    subst out
    exact fun _ hx => hx
  | succ k ih =>
    obtain ⟨lower, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨earlier, he, h⟩ := Option.bind_eq_some_iff.mp h
    change some (earlier ++ [top]) = some block at h
    cases Option.some.inj h
    rcases List.mem_append.mp hm with hm | hm
    · intro x hx
      exact (nativeLower_core_sublist hl).subset (ih he hm x hx)
    · have heq : out = top := by simpa using hm
      subst out
      exact fun _ hx => hx

theorem nativeBlock_nonempty_core_subset {r : Nat} {row out : Row} {sources : List Nat} {block : Pattern}
    (hne : sources ≠ []) (h : nativeBlock row r sources = some block) (hm : out ∈ block) :
    ∀ x ∈ out.core, x ∈ (nativeTop row r sources).core := by
  apply nativeBlockDown_core_subset (hm := hm)
  simpa [nativeBlock, hne] using h

theorem native_block_bottom_b_bound {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r oldB newB : Nat} {row bottom : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (hsrc : nativeSources a r = some sources)
    (hne : sources ≠ []) (hblock : nativeBlock row r sources = some block)
    (hbottom : bottom ∈ block) (hvbottom : bottom.CoreValid r)
    (hb : row.b = some oldB) (hbnew : bottom.b = some newB) : newB ≤ oldB := by
  have hv := valid r row hr
  have hnewlt := fromRight_lt_last hvbottom.1 hvbottom.2.2.1 (by decide : 1 < 2) hbnew
  have hnewidx : bottom.core[bottom.core.length - 2]? = some newB := by
    simpa [Row.b, fromRight, show 2 ≤ bottom.core.length from hvbottom.2.1] using hbnew
  have hmem := nativeBlock_nonempty_core_subset hne hblock hbottom newB (List.mem_of_getElem? hnewidx)
  rcases (nativeTop_core_mem row r sources newB).mp hmem with hold | hsource | htarget
  · exact core_entry_le_b hv hb hold hnewlt
  · have hstep : 1 < row.step := nativeSources_nonempty_step_ge_two hv hr hsrc hne
    have hroom := Row.step_lt_length hv.2.2.2
    obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
    obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) (by omega) (by omega)
    have hbelow := (nativeSources_between valid hr hp he hsrc newB hsource).2
    have helt := fromRight_lt_last hv.1 hv.2.2.1 hstep he
    have heim : e ∈ row.core := by
      unfold fromRight at he
      split at he
      next => exact List.mem_of_getElem? he
      next => simp at he
    have heb := core_entry_le_b hv hb heim helt
    omega
  · omega

theorem native_bottom_b_le {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r oldB newB : Nat} {row bottom : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : native a r = some (b, sources))
    (hne : sources ≠ []) (hbottom : rowAt b r = some bottom)
    (hb : row.b = some oldB) (hbnew : bottom.b = some newB) : newB ≤ oldB := by
  have hvbottom := native_preserves_coreValid valid hn r bottom hbottom
  have hsrc := native_sources_of_success hn
  have hout := hn
  unfold native at hout
  rw [hr] at hout
  dsimp only [Bind.bind, Option.bind] at hout
  rw [hsrc] at hout
  dsimp only [Bind.bind, Option.bind] at hout
  obtain ⟨block, hblock, hout⟩ := Option.bind_eq_some_iff.mp hout
  have hpattern := (Prod.mk.inj (Option.some.inj hout)).1
  have hlen := nativeBlock_length hblock
  have hi : 0 < block.length := by omega
  have hlookup := native_block_rowAt (sources := sources) hr hi
  have hget : block[0]? = some bottom := by
    have heq : rowAt b r = block[0]? := by simpa only [hpattern, Nat.add_zero] using hlookup
    exact heq.symm.trans hbottom
  exact native_block_bottom_b_bound valid hr hsrc hne hblock (List.mem_of_getElem? hget) hvbottom hb hbnew

end FullMarkedBLP


