import FullMarkedBLP.NativeTopSourceCases

namespace FullMarkedBLP

theorem rankRealization_native_top_edges {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (hne : sources ≠ []) :
    (nativeTop row r sources).RealizesEdges
      (rankOrdinalAction (nativeEmbeddingValues embedding r sources.length (r + sources.length)))
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
      (r + sources.length) := by
  intro k x y hx hy
  have hv := h.valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  rcases nativeTop_edge_source_cases h.valid hr hs hy with hk | ⟨z, hz, hk⟩ | hk
  · have hk0 : k < row.core.length := by omega
    have hk1 : k + row.step < row.core.length := by omega
    have hu : row.core[k]? = some row.core[k] := List.getElem?_eq_getElem hk0
    have hv' : row.core[k + row.step]? = some row.core[k + row.step] :=
      List.getElem?_eq_getElem hk1
    obtain ⟨hu', hv''⟩ := nativeTop_all_old_core_pair_indices h.valid hr hp he hs hne hu hv'
    have hx' := full_entry_of_core (owner := r + sources.length) hu'
    have hy' := full_entry_of_core (owner := r + sources.length) hv''
    have ex : x = row.core[k] := Option.some.inj (hx.symm.trans hx')
    have ey : y = row.core[k + row.step] := Option.some.inj (hy.symm.trans hy')
    subst x
    subst y
    rw [nativeEmbeddingValues_block embedding r sources.length sources.length (Nat.le_refl _),
      nativeColumnValues_before theta _ (core_entry_le_owner hv (List.mem_of_getElem? hu)),
      nativeColumnValues_before theta _ (core_entry_le_owner hv (List.mem_of_getElem? hv'))]
    exact h.edges r row hr k _ _ (full_entry_of_core hu) (full_entry_of_core hv')
  · obtain ⟨hz0, hz1⟩ := nativeTop_inserted_pair_indices h.valid hr hp he hs hz
    rw [hk] at hx hy
    have ex : x = z := Option.some.inj (hx.symm.trans (full_entry_of_core hz0))
    have ey : y = r + 1 + (sources.filter (· < z)).length :=
      Option.some.inj (hy.symm.trans (full_entry_of_core hz1))
    subst x
    subst y
    rw [nativeEmbeddingValues_block embedding r sources.length sources.length (Nat.le_refl _)]
    have hp' := rankRealization_native_inserted_pair h hr hs hz (fun _ => embedding r)
    rw [nativeColumnValues_before embedding _ (Nat.le_refl r)] at hp'
    exact hp'
  · have hei : row.core[row.core.length - row.step]? = some e := by
      simpa [Row.e, fromRight, hv.2.2.2.1, hroom.le] using he
    have he' := nativeTop_high_entry h.valid hr hp he hs hei (Nat.le_refl e)
    rw [hk] at hx hy
    have ex : x = e := Option.some.inj (hx.symm.trans (full_entry_of_core he'))
    have hlen := nativeTop_actual_length h.valid hr hs
    have hi : row.core.length - row.step + sources.length + (nativeTop row r sources).step =
        (nativeTop row r sources).core.length := by
      change _ + (row.step + sources.length) = _
      omega
    rw [hi] at hy
    have ey : y = r + sources.length + 1 := by
      simpa [Row.full] using hy.symm
    subst x
    subst y
    exact (rankRealization_native_top_endpoint h hr hp he hs).2

end FullMarkedBLP

