import FullMarkedBLP.ScanSatPrefix

namespace FullMarkedBLP

theorem completeMarkRow_e {row : Row} {owner y e : Nat} {sources : List Nat}
    (hv : row.CoreValid owner) (heOld : row.e = some e)
    (hs : sources.Nodup) (hdis : ∀ z ∈ sources, z ∉ row.core)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hey : e ≤ y) (hbelow : ∀ z ∈ sources, z < e) :
    (completeMarkRow row y sources).e = some e := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hpositive := hv.2.2.2.1
  have hi : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hpositive, show row.step ≤ row.core.length by omega] using heOld
  have he := completeMarkRow_middle_entry hv.1 hs hdis ht hi hey hbelow
  have hst : ∀ z ∈ sources, z ≤ y := by intro z hz; have := hbelow z hz; omega
  have hl := completeMarkRow_length (hv.1.imp (fun h => Nat.ne_of_lt h)) hs hdis hst ht
  have hstep : (completeMarkRow row y sources).step = row.step + sources.length := rfl
  have hidx : row.core.length + 2 * sources.length - (row.step + sources.length) =
      row.core.length - row.step + sources.length := by omega
  simpa [Row.e, fromRight, hpositive, show 0 < row.step + sources.length by omega, hl, hstep, hidx,
    show row.step + sources.length ≤ row.core.length + 2 * sources.length by omega] using he


/-- Under the explicit completion geometry, the current row keeps its Sat witness. -/
theorem completion_preserves_owner_sat {a : Pattern} {row : Row}
    {owner y p e : Nat} {sources : List Nat}
    (hv : row.CoreValid owner) (hr : rowAt a owner = some row)
    (hp : row.p = some p) (he : row.e = some e)
    (hs : sources.Nodup) (hdis : ∀ z ∈ sources, z ∉ row.core)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hey : e ≤ y) (hyowner : y < owner) (hbelow : ∀ z ∈ sources, z < p)
    (hw : ∃ er v, rowAt a e = some er ∧ er.b = some v ∧ v ≤ p) :
    (completeMarkRow row y sources).p = some p ∧
    (completeMarkRow row y sources).e = some e ∧
    ∃ er v, rowAt (a.set (owner - 1) (completeMarkRow row y sources)) e = some er ∧
      er.b = some v ∧ v ≤ p := by
  have hpe := row_p_lt_e hv hp he
  have hpnew := completeMarkRow_p hv hp hs hdis ht (by omega) hbelow
  have henew := completeMarkRow_e hv he hs hdis ht hey
    (fun z hz => by have hh := hbelow z hz; omega)
  obtain ⟨er, v, her, hb, hvp⟩ := hw
  exact ⟨hpnew, henew, er, v, (rowAt_set_other hr (by omega : e ≠ owner)).trans her, hb, hvp⟩

end FullMarkedBLP

