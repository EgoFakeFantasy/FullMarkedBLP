import FullMarkedBLP.NativeSourceTrace

namespace FullMarkedBLP

/-- The first new marked target has the old p-column as its step-source. -/
theorem nativeTop_owner_source {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p)
    (h : nativeSources a r = some sources) :
    ∃ k, (nativeTop row r sources).step ≤ k ∧
      (nativeTop row r sources).core[k]? = some r ∧
      (nativeTop row r sources).core[k - (nativeTop row r sources).step]? = some p := by
  have hv := valid r row hr
  have hlen := Row.step_lt_length hv.2.2.2
  have hend : row.core[row.core.length - 1]? = some r := by
    simpa [List.getLast?_eq_getElem?] using hv.2.2.1
  have hf : sources.filter (· < r) = sources := by
    apply List.filter_eq_self.mpr
    intro x hx
    simpa using nativeSources_below_owner valid hr h x hx
  have hrank := nativeTop_rank_exact valid hr h (Nat.le_refl r)
  rw [hf, sorted_rank_at_index hv.1 hend] at hrank
  have hm : r ∈ (nativeTop row r sources).core :=
    (nativeTop_core_mem row r sources r).mpr (Or.inl (List.mem_of_getLast? hv.2.2.1))
  have hg := sorted_get_at_rank (nativeTop_sorted row r sources).1 hm
  rw [hrank] at hg
  refine ⟨row.core.length - 1 + sources.length, ?_, hg, ?_⟩
  · change row.step + sources.length ≤ _; omega
  · have heq : row.core.length - 1 + sources.length -
        (nativeTop row r sources).step = row.core.length - (row.step + 1) := by
      change _ - (row.step + sources.length) = _; omega
    rw [heq]
    exact nativeTop_old_p_entry valid hr hp h

theorem nativeTop_owner_mark {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    (hne : sources ≠ []) : r ∈ (nativeTop row r sources).marks := by
  have hlen : 0 < sources.length := List.length_pos_iff.mpr hne
  have hnmem : r ∉ sources := by
    intro hm
    have hh := nativeSources_below_owner valid hr h r hm
    omega
  simp only [nativeTop, mem_canonicalColumns, List.mem_filter]
  constructor
  · apply List.mem_append.mpr
    exact Or.inr (List.mem_map.mpr ⟨0, by simp [hlen], by simp⟩)
  · simp [hnmem, hne]

theorem nativeBlockDown_last {k owner : Nat} {medium : Bool} {top : Row} {block : Pattern}
    (h : nativeBlockDown k owner medium top = some block) : block.getLast? = some top := by
  cases k with
  | zero => simpa [nativeBlockDown] using congrArg (fun o => o.bind List.getLast?) h.symm
  | succ k =>
    obtain ⟨lower, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨earlier, _, h⟩ := Option.bind_eq_some_iff.mp h
    change some (earlier ++ [top]) = some block at h
    cases Option.some.inj h
    simp

theorem native_top_rowAt {a b : Pattern} {r : Nat} {sources : List Nat}
    {row : Row} (hr : rowAt a r = some row)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) :
    rowAt b (r + sources.length) = some (nativeTop row r sources) := by
  unfold native at hn
  rw [hr] at hn
  dsimp only [Bind.bind, Option.bind] at hn
  obtain ⟨ss, _, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨block, hb, hn⟩ := Option.bind_eq_some_iff.mp hn
  change some (_, ss) = some (b, sources) at hn
  cases Option.some.inj hn
  have hl := nativeBlock_length hb
  rw [native_block_rowAt hr (by omega : sources.length < block.length)]
  have ht : block.getLast? = some (nativeTop row r sources) := by
    apply nativeBlockDown_last
    simpa [nativeBlock, hne] using hb
  have he : block.length - 1 = sources.length := by omega
  simpa [List.getLast?_eq_getElem?, he] using ht

/-- The first newly introduced top-row mark has its literal two-node trace. -/
theorem native_top_owner_markTrace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p)
    (hs : nativeSources a r = some sources)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) :
    MarkTrace b (r + sources.length) r [r, p] := by
  obtain ⟨k, hk, ht, hsrc⟩ := nativeTop_owner_source valid hr hp hs
  have hpred : predecessor a r = some p := by simp [predecessor, hr, hp]
  refine ⟨nativeTop row r sources, k, p, native_top_rowAt hr hn hne,
    nativeTop_owner_mark valid hr hs hne, hk, ht, hsrc, ?_⟩
  exact Trace.next (predecessor_lt valid hpred)
    (native_owner_predecessor valid hn hpred) Trace.stop

end FullMarkedBLP



