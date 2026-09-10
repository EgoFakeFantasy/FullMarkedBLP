import FullMarkedBLP.CopyIndex

namespace FullMarkedBLP

theorem copiedRow_mark_origin {a : Pattern} {last row copied : Row} {source x : Nat}
    (h : copiedRow a last source row = some copied) (hx : x ∈ copied.marks) :
    ∃ k y, y ∈ row.marks ∧ row.core[k]? = some y ∧ copied.core[k]? = some x ∧
      copyEntry a.length last y = some x ∧ copyMarkAllowed a source y copied.core k row.step = true := by
  obtain ⟨core, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  obtain ⟨⟨⟨y, z⟩, k⟩, hmem, hfilter⟩ := List.mem_filterMap.mp hx
  dsimp only at hfilter
  split at hfilter
  next hguard =>
    have he : z = x := Option.some.inj hfilter
    subst z
    have hg := Bool.and_eq_true_iff.mp hguard
    have hpair : (row.core.zip core)[k]? = some (y, x) := by
      simpa using (List.mk_mem_zipIdx_iff_getElem?.mp hmem)
    obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hpair
    have hleft := congrArg Prod.fst hv
    have hright := congrArg Prod.snd hv
    simp only [List.getElem_zip] at hleft hright
    have hkl : k < row.core.length := by simp at hi; omega
    have hkr : k < core.length := by simp at hi; omega
    have hyi : row.core[k]? = some y := List.getElem?_eq_some_iff.mpr ⟨hkl, hleft⟩
    have hxi : core[k]? = some x := List.getElem?_eq_some_iff.mpr ⟨hkr, hright⟩
    obtain ⟨original, ho, hmap⟩ := (copiedCore_maps_entries hc).at hxi
    have he := Option.some.inj (ho.symm.trans hyi)
    subst original
    exact ⟨k, y, by simpa using hg.1, hyi, hxi, hmap, hg.2⟩
  next => simp at hfilter

/-- Every selected mark stays in its proper step-target position and before the copied owner. -/
theorem copiedRow_mark_position {a : Pattern} {last row copied : Row} {source owner x : Nat}
    (hv : last.CoreValid a.length) (hr : row.CoreValid source) (hm : row.ProperMarks source)
    (howner : copyEntry a.length last source = some owner)
    (h : copiedRow a last source row = some copied) (hx : x ∈ copied.marks) :
    x < owner ∧ ∃ k, copied.step ≤ k ∧ copied.core[k]? = some x := by
  obtain ⟨k, y, hym, hky, hkx, hmap, _⟩ := copiedRow_mark_origin h hx
  obtain ⟨hyb, j, hj, hjy⟩ := hm.2 y hym
  have hk : k = j := by
    have hf := sorted_findIdx hr.1 hky
    have hg := sorted_findIdx hr.1 hjy
    exact Option.some.inj (hf.symm.trans hg)
  have hstep : copied.step = row.step := by
    obtain ⟨core, _, hout⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj hout
    rfl
  exact ⟨copyEntry_strict hv hyb hmap howner, k, by omega, hkx⟩

end FullMarkedBLP

