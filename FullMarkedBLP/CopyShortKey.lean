import FullMarkedBLP.ShortKeyOrder
import FullMarkedBLP.CopyPredecessor

namespace FullMarkedBLP

theorem Row.owner_mem_drop {row : Row} {owner : Nat} (h : row.CoreValid owner) :
    owner ∈ row.core.drop row.step := by
  have bound := Row.step_lt_length h.2.2.2
  have entry : row.core[row.core.length - 1]? = some owner := by
    simpa only [List.getLast?_eq_getElem?] using h.2.2.1
  have shifted : (row.core.drop row.step)[row.core.length - 1 - row.step]? = some owner := by
    simpa only [List.getElem?_drop, show
      row.step + (row.core.length - 1 - row.step) = row.core.length - 1 by omega] using entry
  exact List.mem_of_getElem? shifted

/-- Every entry in the first copied core is either below the parent minimum
or an entry in its retained high tail. In particular the minimum is omitted. -/
theorem copied_first_core_allowed {a : Pattern} {last row copied : Row} {p minimum : Nat}
    (valid : last.CoreValid a.length) (sourceValid : row.CoreValid p)
    (hp : last.p = some p) (hm : last.core.head? = some minimum)
    (copy : copiedRow a last p row = some copied) :
    ∀ v ∈ copied.core, v < minimum ∨ v ∈ last.core.drop last.step := by
  obtain ⟨core, hc, copy⟩ := Option.bind_eq_some_iff.mp copy
  cases Option.some.inj copy
  intro v hv
  obtain ⟨x, hx, map⟩ := (copiedCore_maps_entries hc).mem_right hv
  have bound := core_entry_le_owner sourceValid hx
  obtain ⟨minimum', p', e, hm', hp', _, _, _, cases⟩ := copyEntry_cases map
  have minimumEq := Option.some.inj (hm'.symm.trans hm)
  have pEq := Option.some.inj (hp'.symm.trans hp)
  subst minimum'; subst p'
  rcases cases with ⟨low, eq⟩ | ⟨_, high, eq⟩ | ⟨_, _, k, _, entry⟩
  · exact Or.inl (by omega)
  · have parentBound := fromRight_le_last valid.1 valid.2.2.1 (by omega) hp
    have eqOwner : v = a.length := by omega
    exact Or.inr (eqOwner ▸ Row.owner_mem_drop valid)
  · apply Or.inr
    have shifted : (last.core.drop last.step)[k]? = some v := by
      simpa only [List.getElem?_drop, Nat.add_comm] using entry
    exact List.mem_of_getElem? shifted

theorem copied_first_shortKey_lt {a : Pattern} {last row copied : Row} {p : Nat}
    (valid : last.CoreValid a.length) (sourceValid : row.CoreValid p)
    (hp : last.p = some p) (copy : copiedRow a last p row = some copied) :
    copied.shortKey < last.shortKey := by
  obtain ⟨owner, _, copiedValid⟩ := copiedRow_coreValid valid sourceValid copy
  obtain ⟨minimum, hm⟩ : ∃ minimum, last.core.head? = some minimum := by
    cases hc : last.core with
    | nil => have := valid.2.1; simp [hc] at this
    | cons x xs => exact ⟨x, by simp⟩
  apply row_shortKey_lt_of_allowed copiedValid.1 copiedValid.2.2.2.1
    valid.1 valid.2.2.2.1 hm
  intro x hx
  exact copied_first_core_allowed valid sourceValid hp hm copy x (Row.shortKey_mem_core hx)

end FullMarkedBLP
