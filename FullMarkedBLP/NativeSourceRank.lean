import FullMarkedBLP.NativeTraceShift

namespace FullMarkedBLP

/-- Every point strictly between adjacent entries has the same insertion rank. -/
theorem rank_between_adjacent {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {i p e x : Nat} (hp : xs[i]? = some p) (he : xs[i + 1]? = some e)
    (hpx : p < x) (hxe : x < e) :
    (xs.filter (· < x)).length = i + 1 := by
  have hf : xs.filter (· < x) = xs.filter (· < e) := by
    apply List.filter_congr
    intro y hy
    have hgap := between_adjacent_not_mem (x := y) hs hp he
    by_cases hyx : y < x
    · simp [hyx, show y < e by omega]
    · have hye : ¬ y < e := by
        intro hye
        have hpy : p < y := by omega
        exact hgap hpy hye hy
      simp [hyx, hye]
  rw [hf, sorted_rank_at_index hs he]

theorem nativeSources_between {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (h : nativeSources a r = some sources) : ∀ x ∈ sources, p < x ∧ x < e := by
  unfold nativeSources at h
  rw [hr] at h
  dsimp only [Bind.bind, Option.bind] at h
  split at h
  next =>
    change some [] = some sources at h
    cases Option.some.inj h
    simp
  next =>
    rw [hp] at h
    dsimp only [Bind.bind, Option.bind] at h
    rw [he] at h
    exact nativeSourcesFuel_bounds valid h

/-- A native source's top-core index consists of the old p-prefix and its
rank among the inserted sources. -/
theorem nativeTop_source_entry {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (h : nativeSources a r = some sources) (hx : x ∈ sources) :
    (nativeTop row r sources).core[row.core.length - (row.step + 1) + 1 +
      (sources.filter (· < x)).length]? = some x := by
  have hv := valid r row hr
  have hl := Row.step_lt_length hv.2.2.2
  have hpos := hv.2.2.2.1
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hei : row.core[row.core.length - (row.step + 1) + 1]? = some e := by
    have hi : row.core.length - (row.step + 1) + 1 = row.core.length - row.step := by omega
    simpa [Row.e, fromRight, hpos, show row.step ≤ row.core.length by omega, hi] using he
  have hb := nativeSources_between valid hr hp he h x hx
  have hrank := rank_between_adjacent hv.1 hpi hei hb.1 hb.2
  have hxle := nativeSources_below_owner valid hr h x hx
  have ht := nativeTop_rank_exact valid hr h (Nat.le_of_lt hxle)
  have hm : x ∈ (nativeTop row r sources).core :=
    (nativeTop_core_mem row r sources x).mpr (Or.inr (Or.inl hx))
  have hg := sorted_get_at_rank (nativeTop_sorted row r sources).1 hm
  simpa only [ht, hrank] using hg

/-- Each inserted source is the predecessor of the corresponding new row. -/
theorem nativeBlock_source_p {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e x : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (h : nativeSources a r = some sources) (hx : x ∈ sources)
    (hb : nativeBlock row r sources = some block) :
    (block[(sources.filter (· < x)).length + 1]?).bind Row.p = some x := by
  have hne : sources ≠ [] := by intro hh; simp [hh] at hx
  have hlt : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have hlen := nativeBlock_length hb
  have hi : (sources.filter (· < x)).length + 1 < block.length := by omega
  have hpred := nativeBlock_actual_p valid hr h hne hb _ hi
  have hent := nativeTop_source_entry valid hr hp he h hx
  have heq : row.core.length - (row.step + 1) + ((sources.filter (· < x)).length + 1) =
      row.core.length - (row.step + 1) + 1 + (sources.filter (· < x)).length := by omega
  simpa only [List.getElem?_eq_getElem hi, Option.bind_some, heq, hent] using hpred

end FullMarkedBLP


