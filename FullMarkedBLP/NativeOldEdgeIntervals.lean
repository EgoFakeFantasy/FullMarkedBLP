import FullMarkedBLP.NativeTopOldEdgeIndices

namespace FullMarkedBLP

theorem eligible_core_edge_intervals {row : Row} {r p e k x y : Nat}
    (hv : row.CoreValid r) (helig : row.core.length ≤ 2 * row.step)
    (hp : row.p = some p) (he : row.e = some e)
    (hx : row.core[k]? = some x) (hy : row.core[k + row.step]? = some y) :
    x ≤ p ∧ e ≤ y := by
  have hxp := step_source_le_p hv hy
    (show row.core[k + row.step - row.step]? = some x by simpa using hx) hp
  refine ⟨hxp, ?_⟩
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hv.2.2.2.1, (Row.step_lt_length hv.2.2.2).le] using he
  by_contra hnot
  have hidx := sorted_index_lt_of_value_lt hv.1 hy hei (by omega : y < e)
  omega

/-- Every old core-to-core edge in a nonempty native input has aligned top
indices; its low/high interval conditions are derived rather than assumed. -/
theorem nativeTop_all_old_core_pair_indices {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e k x y : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (hne : sources ≠ [])
    (hx : row.core[k]? = some x) (hy : row.core[k + row.step]? = some y) :
    (nativeTop row r sources).core[k]? = some x ∧
    (nativeTop row r sources).core[k + (nativeTop row r sources).step]? = some y := by
  have hb := eligible_core_edge_intervals (valid r row hr)
    (nativeSources_nonempty_eligible hr hs hne) hp he hx hy
  exact nativeTop_old_pair_indices valid hr hp he hs hx hy hb.1 hb.2

end FullMarkedBLP
