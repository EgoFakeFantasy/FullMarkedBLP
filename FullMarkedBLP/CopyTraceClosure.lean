import FullMarkedBLP.CopyRowTraces

namespace FullMarkedBLP

theorem shortCopy_preserves_traces {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (traces : ∀ r row, rowAt a r = some row → row.HasTraces a)
    (hcopy : shortCopy a = some b) :
    ∀ r row, rowAt b r = some row → row.HasTraces b := by
  intro r row hr
  by_cases hprefix : r < a.length
  · have ha : rowAt a r = some row := (shortCopy_prefix_rowAt hcopy hprefix).symm.trans hr
    intro y hy
    obtain ⟨k, s, word, hk, hky, hks, ht⟩ := traces r row ha y hy
    have hyr := (marks r row ha).2 y hy
    exact ⟨k, s, word, hk, hky, hks, shortCopy_prefix_trace valid hcopy ht (by omega)⟩
  · have h := hcopy
    unfold shortCopy at h
    split at h
    next => simp at h
    next hlen =>
      obtain ⟨last, hl, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sources, hs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨copied, hc, h⟩ := Option.bind_eq_some_iff.mp h
      have hb : a.dropLast ++ copied = b := Option.some.inj h
      have hr' : rowAt (a.dropLast ++ copied) r = some row := by simpa only [hb] using hr
      have hz : r ≠ 0 := by omega
      have hge : a.dropLast.length ≤ r - 1 := by simp; omega
      have hget : copied[r - 1 - a.dropLast.length]? = some row := by
        simpa only [rowAt, hz, ↓reduceIte, List.getElem?_append_right hge] using hr'
      have hmem := List.mem_of_getElem? hget
      obtain ⟨source, hsource, hrow⟩ := (option_mapM_forall2 hc).mem_right hmem
      obtain ⟨old, hold, hout⟩ := Option.bind_eq_some_iff.mp hrow
      obtain ⟨p, e, _, he, _, hsrc⟩ := shortCopySources_description hs
      have hsource' : source ∈ (List.range (e - p)).map (p + ·) := by simpa only [hsrc] using hsource
      obtain ⟨i, hi, hiEq⟩ := List.mem_map.mp hsource'
      have hir : i < e - p := List.mem_range.mp hi
      have hse : source ≤ e := by omega
      have hlast : rowAt a a.length = some last := by
        simpa [rowAt, show a.length ≠ 0 by omega, List.getLast?_eq_getElem?] using hl
      exact copiedRow_hasTraces valid hcopy hl he hse (valid _ _ hlast)
        (marks _ _ hlast) (traces _ _ hlast) hold (marks _ _ hold) hout

end FullMarkedBLP
