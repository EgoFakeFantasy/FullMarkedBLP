import FullMarkedBLP.CopySatInternal

namespace FullMarkedBLP

/-- Every eligible output row with a predecessor in the copied region has an actual Sat witness. -/
theorem shortCopy_internal_sat {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (hcopy : shortCopy a = some b)
    {r q : Nat} {row : Row} (hr : rowAt b r = some row)
    (hq : row.p = some q) (hhigh : a.length ≤ q)
    (heligible : row.core.length ≤ 2 * row.step) :
    ∃ e er v, row.e = some e ∧ rowAt b e = some er ∧ er.b = some v ∧ v ≤ q := by
  have hvout := shortCopy_preserves_coreValid valid hcopy r row hr
  have hqr := fromRight_lt_last hvout.1 hvout.2.2.1
    (by have := hvout.2.2.2.1; omega : 1 < row.step + 1) hq
  have h := hcopy
  unfold shortCopy at h
  split at h
  next => simp at h
  next hlen =>
    obtain ⟨last, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sources, hsources, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨copied, hc, h⟩ := Option.bind_eq_some_iff.mp h
    have hb : a.dropLast ++ copied = b := Option.some.inj h
    have hr' : rowAt (a.dropLast ++ copied) r = some row := by simpa only [hb] using hr
    have hz : r ≠ 0 := by omega
    have hge : a.dropLast.length ≤ r - 1 := by simp; omega
    have hget : copied[r - 1 - a.dropLast.length]? = some row := by
      simpa only [rowAt, hz, ↓reduceIte, List.getElem?_append_right hge] using hr'
    obtain ⟨source, hsource, hrow⟩ := (option_mapM_forall2 hc).mem_right (List.mem_of_getElem? hget)
    obtain ⟨old, hold, hout⟩ := Option.bind_eq_some_iff.mp hrow
    obtain ⟨p, e, hp, he, _, hsrc⟩ := shortCopySources_description hsources
    have hsource' : source ∈ (List.range (e - p)).map (p + ·) := by simpa only [hsrc] using hsource
    obtain ⟨i, hi, hiEq⟩ := List.mem_map.mp hsource'
    have hir : i < e - p := List.mem_range.mp hi
    have hlast : rowAt a a.length = some last := by
      simpa [rowAt, show a.length ≠ 0 by omega, List.getLast?_eq_getElem?] using hl
    have holdeligible : old.core.length ≤ 2 * old.step := by
      obtain ⟨core, hcore, heq⟩ := Option.bind_eq_some_iff.mp hout
      cases Option.some.inj heq
      simpa only [copiedCore_length hcore] using heligible
    obtain ⟨q', e', er, v, hq', he', her, hv, hvq⟩ := shortCopy_sat_output_predecessor
      hs hcopy hl hp he (valid _ _ hlast) (valid _ _ hold) hold hout holdeligible hq hhigh (by omega)
    have hqq := Option.some.inj (hq'.symm.trans hq)
    exact ⟨e', er, v, he', her, hv, by omega⟩

end FullMarkedBLP
