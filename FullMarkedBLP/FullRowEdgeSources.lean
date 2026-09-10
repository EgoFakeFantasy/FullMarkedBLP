import FullMarkedBLP.CompletionSemanticIntervals

namespace FullMarkedBLP

/-- Every full-row edge begins in the core, at or before e. -/
theorem full_edge_source_bound {row : Row} {r i x z e : Nat}
    (hv : row.CoreValid r) (he : row.e = some e)
    (hx : (row.full r)[i]? = some x) (hz : (row.full r)[i + row.step]? = some z) :
    row.core[i]? = some x ∧ x ≤ e := by
  have hzlen := (List.getElem?_eq_some_iff.mp hz).1
  simp only [Row.full, List.length_append, List.length_singleton] at hzlen
  have hstep := hv.2.2.2.1
  have hi : i < row.core.length := by omega
  have hxc : row.core[i]? = some x := by
    simpa only [Row.full, List.getElem?_append_left hi] using hx
  have hroom := Row.step_lt_length hv.2.2.2
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hstep, hroom.le] using he
  refine ⟨hxc, ?_⟩
  by_cases hidx : i = row.core.length - row.step
  · rw [hidx, hei] at hxc
    exact le_of_eq (Option.some.inj hxc).symm
  · obtain ⟨hii, hix⟩ := List.getElem?_eq_some_iff.mp hxc
    obtain ⟨hei', hie⟩ := List.getElem?_eq_some_iff.mp hei
    have hh := List.pairwise_iff_getElem.mp hv.1 _ _ hii hei' (by omega)
    exact le_of_lt (by simpa only [hix, hie] using hh)

/-- Every old core value at or below e really is an old full-edge source. -/
theorem full_edge_exists_of_source_le_e {row : Row} {r x e : Nat}
    (hv : row.CoreValid r) (he : row.e = some e) (hx : x ∈ row.core) (hxe : x ≤ e) :
    ∃ i z, (row.full r)[i]? = some x ∧ (row.full r)[i + row.step]? = some z := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have hroom := Row.step_lt_length hv.2.2.2
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hv.2.2.2.1, hroom.le] using he
  have hib : i ≤ row.core.length - row.step := by
    by_contra hn
    obtain ⟨hii, hix⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hei', hie⟩ := List.getElem?_eq_some_iff.mp hei
    have hh := List.pairwise_iff_getElem.mp hv.1 _ _ hei' hii (by omega)
    rw [hie, hix] at hh
    omega
  have hbound : i + row.step < (row.full r).length := by
    simp only [Row.full, List.length_append, List.length_singleton]
    omega
  refine ⟨i, (row.full r)[i + row.step], full_entry_of_core hi, ?_⟩
  simp [hbound]

end FullMarkedBLP

