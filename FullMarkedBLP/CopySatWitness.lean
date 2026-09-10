import FullMarkedBLP.CopyRecordRegion

namespace FullMarkedBLP

theorem copiedRow_e {a : Pattern} {last row copied : Row} {source e : Nat}
    (he : row.e = some e) (h : copiedRow a last source row = some copied) :
    ∃ e', copied.e = some e' ∧ copyEntry a.length last e = some e' := by
  obtain ⟨core, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  exact (copiedCore_maps_entries hc).fromRight he

theorem copiedRow_b {a : Pattern} {last row copied : Row} {source v : Nat}
    (hb : row.b = some v) (h : copiedRow a last source row = some copied) :
    ∃ v', copied.b = some v' ∧ copyEntry a.length last v = some v' := by
  obtain ⟨core, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  exact (copiedCore_maps_entries hc).fromRight hb

theorem copyEntry_le {n x y x' y' : Nat} {last : Row}
    (hv : last.CoreValid n) (hle : x ≤ y)
    (hx : copyEntry n last x = some x') (hy : copyEntry n last y = some y') : x' ≤ y' := by
  by_cases he : x = y
  · subst y
    have hh := Option.some.inj (hx.symm.trans hy)
    omega
  · have hh := copyEntry_strict hv (by omega : x < y) hx hy
    omega

/-- Sat witnesses transport when the endpoint row is itself in the copied source interval. -/
theorem shortCopy_sat_copied_endpoint {a b : Pattern} {last row copied : Row}
    {r threshold upper : Nat}
    (hs : Sat a) (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some threshold) (he : last.e = some upper)
    (hv : last.CoreValid a.length) (htn : threshold ≤ a.length)
    (hr : rowAt a r = some row) (hc : copiedRow a last r row = some copied)
    (heligible : row.core.length ≤ 2 * row.step)
    (hend : ∀ e, row.e = some e → threshold ≤ e ∧ e < upper) :
    ∃ p' e' er' v', copied.p = some p' ∧ copied.e = some e' ∧
      rowAt b e' = some er' ∧ er'.b = some v' ∧ v' ≤ p' := by
  obtain ⟨p, e, er, v, hrp, hre, her, hb, hle⟩ := hs r row hr heligible
  obtain ⟨p', hpp, hpm⟩ := copiedRow_p hrp hc
  obtain ⟨e', hee, hem⟩ := copiedRow_e hre hc
  have heRange := hend e hre
  obtain ⟨old, er', hold, hercopy, herout⟩ := shortCopy_copied_rowAt h hl hp he heRange.1 heRange.2 htn
  have hold' := Option.some.inj (hold.symm.trans her)
  subst old
  obtain ⟨v', hvv, hvm⟩ := copiedRow_b hb hercopy
  have heq := copyEntry_high_value hv hp heRange.1 hem
  exact ⟨p', e', er', v', hpp, hee, by simpa only [heq] using herout,
    hvv, copyEntry_le hv hle hvm hpm⟩

end FullMarkedBLP

