import FullMarkedBLP.NativeActualBlockMinimum

namespace FullMarkedBLP

theorem rankRealization_native_replacement_critical {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r minimum : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hm : row.core.head? = some minimum)
    (hn : native a r = some (b, sources)) (hne : sources ≠ [])
    {i : Nat} {target : Row} (hi : r ≤ i) (hi' : i ≤ r + sources.length)
    (ht : rowAt b i = some target) :
    target.core.head? = some minimum ∧
    RankCriticalPoint (nativeEmbeddingValues embedding r sources.length i)
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length minimum) := by
  have hn' := hn
  unfold native at hn'
  rw [hr] at hn'
  dsimp only [Bind.bind, Option.bind] at hn'
  obtain ⟨ss, hs, hn'⟩ := Option.bind_eq_some_iff.mp hn'
  obtain ⟨block, hb, hn'⟩ := Option.bind_eq_some_iff.mp hn'
  change some (_, ss) = some (b, sources) at hn'
  cases Option.some.inj hn'
  obtain ⟨actual, ha, ham⟩ := rankRealization_native_actual_block_minimum h hr hm hn hne
  have heq := Option.some.inj (hb.symm.trans ha)
  subst actual
  have hl := nativeBlock_length hb
  have hj : i - r < block.length := by omega
  have hiEq : i = r + (i - r) := by omega
  have ht' := ht
  rw [hiEq, native_block_rowAt hr hj] at ht'
  obtain ⟨hidx, hv⟩ := List.getElem?_eq_some_iff.mp ht'
  have hmin := ham (i - r) hidx
  rw [hv] at hmin
  refine ⟨hmin, ?_⟩
  have hei : nativeEmbeddingValues embedding r sources.length i = embedding r := by
    rw [hiEq]
    exact nativeEmbeddingValues_block embedding r sources.length (i - r) (by omega)
  have hmr := core_entry_le_owner (h.valid r row hr) (List.mem_of_head? hm)
  rw [hei, nativeColumnValues_before theta _ hmr]
  exact h.critical r row minimum hr hm

end FullMarkedBLP

