import FullMarkedBLP.NativeTraceShift
import FullMarkedBLP.NativeSatClosure

namespace FullMarkedBLP

/-- Native transports endpoints of old rows unless that row creates a nonempty block. -/
theorem native_unexpanded_endpoint_shift {a b : Pattern}
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    {r i e : Nat} {sources : List Nat} {row : Row}
    (birth : native a r = some (b, sources)) (hr : rowAt a i = some row)
    (he : row.e = some e) (unexpanded : i ≠ r ∨ sources = []) :
    (rowAt b (shiftAfter r sources.length i)).bind Row.e =
      some (shiftAfter r sources.length e) := by
  by_cases empty : sources = []
  · subst sources
    obtain ⟨owner, atOwner, _⟩ := Option.bind_eq_some_iff.mp birth
    have same := native_empty atOwner (native_sources_of_success birth)
    have eq : b = a := (Prod.mk.inj (Option.some.inj (birth.symm.trans same))).1
    subst b
    simpa [shiftAfter, hr] using he
  · have ne : i ≠ r := unexpanded.resolve_right empty
    by_cases later : r < i
    · simp only [shiftAfter, later, if_true]
      rw [native_suffix_rowAt birth later, hr]
      simp only [Option.map_some, Option.bind_some, shifted_row_e, he, Option.map_some]
      rfl
    · have before : i < r := by omega
      have hv := valid i row hr
      have bound : e ≤ i := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
      have fixedI : shiftAfter r sources.length i = i := by simp [shiftAfter, later]
      have fixedE : shiftAfter r sources.length e = e := by simp [shiftAfter, show ¬ r < e by omega]
      rw [fixedI, fixedE, native_prefix_rowAt birth before, hr]
      exact he

end FullMarkedBLP

