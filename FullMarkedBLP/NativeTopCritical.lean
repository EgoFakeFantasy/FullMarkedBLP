import FullMarkedBLP.NativeAllCertificates

namespace FullMarkedBLP

theorem nativeTop_preserves_minimum {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r minimum : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hs : nativeSources a r = some sources)
    (hm : row.core.head? = some minimum) :
    (nativeTop row r sources).core.head? = some minimum := by
  have hv := valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hmp := core_head_le_entry hv hm hpi
  have hm0 : row.core[0]? = some minimum := by simpa only [List.head?_eq_getElem?] using hm
  simpa only [List.head?_eq_getElem?] using nativeTop_low_entry valid hr hp hs hm0 hmp

theorem rankRealization_native_top_critical {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r minimum : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : native a r = some (b, sources))
    (hne : sources ≠ []) (hm : row.core.head? = some minimum) :
    rowAt b (r + sources.length) = some (nativeTop row r sources) ∧
    (nativeTop row r sources).core.head? = some minimum ∧
    RankCriticalPoint (nativeEmbeddingValues embedding r sources.length (r + sources.length))
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length minimum) := by
  refine ⟨native_top_rowAt hr hn hne,
    nativeTop_preserves_minimum h.valid hr (native_sources_of_success hn) hm, ?_⟩
  have hmin := core_entry_le_owner (h.valid r row hr) (List.mem_of_head? hm)
  rw [nativeEmbeddingValues_block embedding r sources.length sources.length (Nat.le_refl _),
    nativeColumnValues_before theta _ hmin]
  exact h.critical r row minimum hr hm

end FullMarkedBLP

