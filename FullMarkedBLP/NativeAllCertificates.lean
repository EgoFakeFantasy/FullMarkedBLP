import FullMarkedBLP.NativeReplacementCertificates

namespace FullMarkedBLP

theorem nativeColumnValues_zero {alpha : Type u} (old fresh : Nat → alpha) (r : Nat) :
    nativeColumnValues old fresh r 0 = old := by
  funext x
  by_cases hx : x ≤ r <;> simp [nativeColumnValues, hx]

/-- All actual output rows retain natural marked certificates under the
concrete native interpretation; this is only the marked component of realization. -/
theorem rankRealization_native_all_certificates {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) :
    ∀ i target, rowAt b i = some target → target.HasRankCertificates b
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
      (nativeEmbeddingValues embedding r sources.length)
      (nativeEmbeddingValues embedding r sources.length i) := by
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  by_cases hne : sources = []
  · subst sources
    have heq := Option.some.inj (hn.symm.trans (native_empty hr (native_sources_of_success hn)))
    have hab : b = a := congrArg Prod.fst heq
    subst b
    simp only [List.length_nil, nativeEmbeddingValues, nativeColumnValues_zero]
    intro i target ht y hy
    exact h.marked i target y ht hy
  · have hv := h.valid r row hr
    have hroom := Row.step_lt_length hv.2.2.2
    obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
    obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
    intro i target ht
    by_cases hi : i < r
    · have hold : rowAt a i = some target := (native_prefix_rowAt hn hi).symm.trans ht
      apply (row_hasRankCertificates_iff ht).mpr
      intro y hy
      exact rankRealization_native_prefix_mark h hr hp he hn hi hold hy (fun _ => embedding r)
    · by_cases hi' : i ≤ r + sources.length
      · exact rankRealization_native_replacement_certificates h hr hp he hn hne (by omega) hi' ht
      · have hj : r < i - sources.length := by omega
        have heq : i - sources.length + sources.length = i := by omega
        have hlookup := native_suffix_rowAt hn hj
        rw [heq, ht] at hlookup
        obtain ⟨old, hold, hv⟩ := Option.map_eq_some_iff.mp hlookup.symm
        subst target
        apply (row_hasRankCertificates_iff ht).mpr
        intro y hy
        obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
        have hc := rankRealization_native_suffix_mark h hr hp he hn hj hold hx (fun _ => embedding r)
        simpa only [heq, hxy, nativeEmbeddingValues] using hc

end FullMarkedBLP


