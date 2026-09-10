import FullMarkedBLP.RealizedInterval

namespace FullMarkedBLP

theorem coreValid_full_sorted {row : Row} {owner : Nat} (hv : row.CoreValid owner) :
    (row.full owner).Pairwise (· < ·) := by
  apply List.pairwise_append.mpr
  refine ⟨hv.1, by simp, ?_⟩
  intro x hx y hy
  have he : y = owner + 1 := by simpa using hy
  have hb := core_entry_le_owner hv hx
  omega

theorem target_position_after_p {row : Row} {owner k y p : Nat}
    (hv : row.CoreValid owner) (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hp : row.p = some p) : p ≤ y := by
  have hlength : row.core.length ≤ 2 * row.step + 1 := by
    rcases hv.2.2.2 with ⟨_, hh | hh | hh⟩ <;> omega
  have hroom := Row.step_lt_length hv.2.2.2
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  by_cases he : row.core.length - (row.step + 1) = k
  · rw [he, hy] at hpi
    exact le_of_eq (Option.some.inj hpi).symm
  · obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp hpi
    obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hy
    have hh := List.pairwise_iff_getElem.mp hv.1 _ _ hi hj (by omega)
    exact le_of_lt (by simpa only [hiv, hjv] using hh)

/-- A new edge targeting below the owner has its source strictly below p. -/
theorem rankRealization_edge_source_below_p {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r p x z : Nat} {row : Row}
    (hr : rowAt a r = some row) (hp : row.p = some p) (hx : x ≤ a.length + 1)
    (hz : z < r) (edge : rankOrdinalAction (embedding r) (theta x) = theta z) : x < p := by
  have hb := (rowAt_bounds hr).2
  have hpbound := fromRight_le_last (h.valid r row hr).1 (h.valid r row hr).2.2.1
    (by omega : 0 < row.step + 1) hp
  have oldEdge := realizesEdges_p (h.valid r row hr) (h.edges r row hr) hp
  have ht : theta x < theta p := (rankOrdinalAction_lt_iff (embedding r) _ _).mp (by
    rw [edge, oldEdge]
    exact h.increasing z r hz (by omega))
  exact (rankRealization_column_lt_iff h hx (by omega)).mp ht

end FullMarkedBLP
