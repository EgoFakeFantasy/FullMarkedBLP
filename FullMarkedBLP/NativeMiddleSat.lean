import FullMarkedBLP.NativeBottomSat

namespace FullMarkedBLP

theorem decreasing_rank_at_index {xs : List Nat} {k x : Nat}
    (hs : xs.Pairwise (· > ·)) (hx : xs[k]? = some x) :
    (xs.filter (· < x)).length = xs.length - 1 - k := by
  induction xs generalizing k with
  | nil => simp at hx
  | cons head tail ih =>
    have hp := List.pairwise_cons.mp hs
    cases k with
    | zero =>
      have he : head = x := by simpa using hx
      subst x
      have hf : tail.filter (· < head) = tail := List.filter_eq_self.mpr
        (fun y hy => by simpa using hp.1 y hy)
      simp [hf]
    | succ k =>
      have hx' : tail[k]? = some x := by simpa using hx
      have hlt := hp.1 x (List.mem_of_getElem? hx')
      have hr := ih hp.2 hx'
      simp only [List.filter_cons, show decide (head < x) = false by simp; omega,
        Bool.false_eq_true, ↓reduceIte, List.length_cons]
      rw [hr]
      omega

theorem nativeSources_adjacent_b {a : Pattern} {r p e i x y : Nat}
    {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hsrc : nativeSources a r = some sources)
    (hx : sources[i]? = some x) (hy : sources[i + 1]? = some y) :
    ∃ er, rowAt a x = some er ∧ er.b = some y := by
  have hne : sources ≠ [] := by intro hh; simp [hh] at hx
  have htail : sources.tail[i]? = some y := by simpa using hy
  have hpair : (x, y) ∈ sources.zip sources.tail := List.mem_of_getElem?
    (List.getElem?_zip_eq_some.mpr ⟨hx, htail⟩)
  have hpair' : (x, y) ∈ (e :: sources).zip sources := by
    cases sources with
    | nil => contradiction
    | cons head tail => exact List.mem_cons_of_mem _ hpair
  exact nativeSourcesFuel_chain_edges (nativeSources_nonempty_fuel hr hp he hsrc hne) x y hpair'

theorem native_middle_sat_witness {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e i x y : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hsrc : nativeSources a r = some sources)
    (hx : sources[i]? = some x) (hy : sources[i + 1]? = some y)
    (hn : native a r = some (b, sources)) :
    ∃ middle er, rowAt b (r + (sources.filter (· < x)).length) = some middle ∧
      middle.p = some y ∧ middle.e = some x ∧ rowAt b x = some er ∧ er.b = some y := by
  have hxm := List.mem_of_getElem? hx
  have hym := List.mem_of_getElem? hy
  have hdec := nativeSources_decreasing valid hsrc
  have hxr := decreasing_rank_at_index hdec hx
  have hyr := decreasing_rank_at_index hdec hy
  have hib := (List.getElem?_eq_some_iff.mp hy).1
  have heq : (sources.filter (· < y)).length + 1 = (sources.filter (· < x)).length := by omega
  obtain ⟨er, her, hb⟩ := nativeSources_adjacent_b hr hp he hsrc hx hy
  have hlow := nativeSources_below_owner valid hr hsrc x hxm
  have her' := (native_prefix_rowAt hn hlow).trans her
  have hout := hn
  unfold native at hout
  rw [hr] at hout
  dsimp only [Bind.bind, Option.bind] at hout
  rw [hsrc] at hout
  dsimp only [Bind.bind, Option.bind] at hout
  obtain ⟨block, hblock, hout⟩ := Option.bind_eq_some_iff.mp hout
  have hpattern := (Prod.mk.inj (Option.some.inj hout)).1
  have hlen := nativeBlock_length hblock
  have hi : (sources.filter (· < x)).length < block.length := by omega
  have hbp := nativeBlock_source_p valid hr hp he hsrc hym hblock
  rw [heq] at hbp
  have hbe := nativeBlock_source_e valid hr hp he hsrc hxm hblock
  have hpout : (block[(sources.filter (· < x)).length]).p = some y := by
    simpa only [List.getElem?_eq_getElem hi, Option.bind_some] using hbp
  have heout : (block[(sources.filter (· < x)).length]).e = some x := by
    simpa only [List.getElem?_eq_getElem hi, Option.bind_some] using hbe
  have hrow := native_block_rowAt (sources := sources) hr hi
  have hrow' : rowAt b (r + (sources.filter (· < x)).length) = some block[(sources.filter (· < x)).length] := by
    simpa only [hpattern, List.getElem?_eq_getElem hi] using hrow
  exact ⟨_, er, hrow', hpout, heout, her', hb⟩

/-- Every row of a nonempty native replacement block has a Sat witness. -/
theorem native_block_sat_witness {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e j : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hsrc : nativeSources a r = some sources) (hne : sources ≠ [])
    (hn : native a r = some (b, sources)) (hj : j ≤ sources.length) :
    ∃ out q endpoint er v, rowAt b (r + j) = some out ∧ out.p = some q ∧
      out.e = some endpoint ∧ rowAt b endpoint = some er ∧ er.b = some v ∧ v ≤ q := by
  have hpositive : 0 < sources.length := List.length_pos_iff.mpr hne
  by_cases hzero : j = 0
  · subst j
    have hi : sources.length - 1 < sources.length := by omega
    have hlast : sources.getLast? = some sources[sources.length - 1] := by
      simp [List.getLast?_eq_getElem?, hi]
    obtain ⟨out, er, v, hout, hq, hep, her, hb, hle⟩ := native_bottom_sat_witness valid hr hp he hsrc hlast hn
    exact ⟨out, p, _, er, v, by simpa using hout, hq, hep, her, hb, hle⟩
  · by_cases htop : j = sources.length
    · subst j
      cases sources with
      | nil => contradiction
      | cons head tail =>
        obtain ⟨hq, hep, er, her, hb⟩ := native_top_sat_witness valid hr hp he hsrc hn
        exact ⟨nativeTop row r (head :: tail), head, e, er, head,
          native_top_rowAt hr hn hne, hq, hep, her, hb, Nat.le_refl _⟩
    · let i := sources.length - 1 - j
      have hi : i < sources.length := by dsimp [i]; omega
      have hi' : i + 1 < sources.length := by dsimp [i]; omega
      have hx : sources[i]? = some sources[i] := by simp [hi]
      have hy : sources[i + 1]? = some sources[i + 1] := by simp [hi']
      have hrank := decreasing_rank_at_index (nativeSources_decreasing valid hsrc) hx
      have heq : (sources.filter (· < sources[i])).length = j := by
        have harith : sources.length - 1 - i = j := by dsimp [i]; omega
        exact hrank.trans harith
      obtain ⟨out, er, hout, hq, hep, her, hb⟩ := native_middle_sat_witness valid hr hp he hsrc hx hy hn
      exact ⟨out, sources[i + 1], sources[i], er, sources[i + 1], by simpa only [heq] using hout,
        hq, hep, her, hb, Nat.le_refl _⟩

end FullMarkedBLP



