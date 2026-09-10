import FullMarkedBLP.NativeTopEndpointRealization

namespace FullMarkedBLP

/-- Each inserted source has its insertion-rank target exactly one new step
later in the literal native top core. -/
theorem nativeTop_inserted_pair_indices {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e x : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (hx : x ∈ sources) :
    let k := row.core.length - row.step + (sources.filter (· < x)).length
    (nativeTop row r sources).core[k]? = some x ∧
    (nativeTop row r sources).core[k + (nativeTop row r sources).step]? =
      some (r + 1 + (sources.filter (· < x)).length) := by
  dsimp only
  have hv := valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  have hsource := nativeTop_source_entry valid hr hp he hs hx
  have hidx : row.core.length - (row.step + 1) + 1 = row.core.length - row.step := by omega
  rw [hidx] at hsource
  refine ⟨hsource, ?_⟩
  have hlt : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have ht := nativeTop_target_entry valid hr hs (j := (sources.filter (· < x)).length + 1) (by omega)
  have heq : row.core.length - row.step + (sources.filter (· < x)).length +
      (nativeTop row r sources).step = row.core.length - 1 + sources.length +
        ((sources.filter (· < x)).length + 1) := by
    change _ + (row.step + sources.length) = _
    omega
  rw [heq]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht

end FullMarkedBLP
