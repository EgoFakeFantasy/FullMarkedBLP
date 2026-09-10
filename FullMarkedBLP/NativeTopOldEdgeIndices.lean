import FullMarkedBLP.NativeBlockEdges

namespace FullMarkedBLP

/-- Every old core entry at or above e moves right by the complete source count. -/
theorem nativeTop_high_entry {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e x k : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (hx : row.core[k]? = some x) (hex : e ≤ x) :
    (nativeTop row r sources).core[k + sources.length]? = some x := by
  have hv := valid r row hr
  have hxm := List.mem_of_getElem? hx
  have hf : sources.filter (· < x) = sources := by
    apply List.filter_eq_self.mpr
    intro z hz
    have hb := (nativeSources_between valid hr hp he hs z hz).2
    simp only [decide_eq_true_eq]
    omega
  have hrank := nativeTop_rank_exact valid hr hs (core_entry_le_owner hv hxm)
  rw [hf, sorted_rank_at_index hv.1 hx] at hrank
  have hmem := (nativeTop_core_mem row r sources x).mpr (Or.inl hxm)
  simpa only [hrank] using sorted_get_at_rank (nativeTop_sorted row r sources).1 hmem

/-- Low-source/high-target old edges align with the increased top step. -/
theorem nativeTop_old_pair_indices {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e k x y : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources)
    (hx : row.core[k]? = some x) (hy : row.core[k + row.step]? = some y)
    (hxp : x ≤ p) (hey : e ≤ y) :
    (nativeTop row r sources).core[k]? = some x ∧
    (nativeTop row r sources).core[k + (nativeTop row r sources).step]? = some y := by
  refine ⟨nativeTop_low_entry valid hr hp hs hx hxp, ?_⟩
  simpa only [nativeTop, Nat.add_assoc] using nativeTop_high_entry valid hr hp he hs hy hey

end FullMarkedBLP
