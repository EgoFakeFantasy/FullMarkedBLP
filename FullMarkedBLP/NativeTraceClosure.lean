import FullMarkedBLP.NativeTracesActual

namespace FullMarkedBLP

theorem native_replacement_traces {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.ProperMarks r)
    (traces : ∀ y ∈ row.marks, ∃ xs, MarkTrace a r y xs)
    (hn : native a r = some (b, sources))
    {i : Nat} {target : Row} (hi : r ≤ i) (hi' : i ≤ r + sources.length)
    (ht : rowAt b i = some target) : target.HasTraces b := by
  have hn' := hn
  unfold native at hn'
  rw [hr] at hn'
  dsimp only [Bind.bind, Option.bind] at hn'
  obtain ⟨ss, hs, hn'⟩ := Option.bind_eq_some_iff.mp hn'
  obtain ⟨block, hb, hn'⟩ := Option.bind_eq_some_iff.mp hn'
  change some (_, ss) = some (b, sources) at hn'
  cases Option.some.inj hn'
  obtain ⟨actual, ha, hat⟩ := nativeBlock_actual_traces valid hr hm hs hn traces
  have he := Option.some.inj (hb.symm.trans ha)
  subst actual
  have hl := nativeBlock_length hb
  have hj : i - r < block.length := by omega
  have hiEq : i = r + (i - r) := by omega
  rw [hiEq, native_block_rowAt hr hj] at ht
  obtain ⟨hidx, hv⟩ := List.getElem?_eq_some_iff.mp ht
  simpa only [hv] using hat (i - r) hidx

/-- Every row of a native output has marked traces when the input does. -/
theorem native_preserves_traces {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (traces : ∀ r row, rowAt a r = some row → row.HasTraces a)
    {r : Nat} {sources : List Nat} (hn : native a r = some (b, sources)) :
    ∀ i target, rowAt b i = some target → target.HasTraces b := by
  intro i target ht
  by_cases hi : i < r
  · have hr : rowAt a i = some target := by simpa only [native_prefix_rowAt hn hi] using ht
    apply (row_hasTraces_iff ht).mpr
    intro y hy
    obtain ⟨xs, htrace⟩ := (row_hasTraces_iff hr).mp (traces i target hr) y hy
    exact ⟨xs, native_prefix_markTrace valid marks hn htrace hi⟩
  · by_cases hi' : i ≤ r + sources.length
    · obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
      exact native_replacement_traces valid hr (marks r row hr)
        ((row_hasTraces_iff hr).mp (traces r row hr)) hn (by omega) hi' ht
    · have hj : r < i - sources.length := by omega
      have he : i - sources.length + sources.length = i := by omega
      have hlookup := native_suffix_rowAt hn hj
      rw [he, ht] at hlookup
      obtain ⟨old, ho, hv⟩ := Option.map_eq_some_iff.mp hlookup.symm
      subst target
      apply (row_hasTraces_iff ht).mpr
      intro y hy
      obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
      obtain ⟨xs, htrace⟩ := (row_hasTraces_iff ho).mp (traces _ old ho) x hx
      have hnew := native_suffix_markTrace valid hn htrace hj
      exact ⟨xs.map (shiftAfter r sources.length), by simpa only [he, hxy] using hnew⟩

end FullMarkedBLP
