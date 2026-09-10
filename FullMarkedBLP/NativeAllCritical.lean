import FullMarkedBLP.NativeReplacementCritical

namespace FullMarkedBLP

theorem rankRealization_native_all_critical {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) :
    ∀ i target minimum, rowAt b i = some target → target.core.head? = some minimum →
      RankCriticalPoint (nativeEmbeddingValues embedding r sources.length i)
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length minimum) := by
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  by_cases hne : sources = []
  · subst sources
    have heq := Option.some.inj (hn.symm.trans (native_empty hr (native_sources_of_success hn)))
    have hab : b = a := congrArg Prod.fst heq
    subst b
    simp only [List.length_nil, nativeEmbeddingValues, nativeColumnValues_zero]
    exact h.critical
  · intro i target minimum ht hm
    by_cases hi : i < r
    · have hold : rowAt a i = some target := (native_prefix_rowAt hn hi).symm.trans ht
      exact (rankRealization_native_prefix_critical h hn hi hold hm (fun _ => embedding r)
        (nativeFreshValues theta (embedding r) r sources)).2
    · by_cases hi' : i ≤ r + sources.length
      · have hv := h.valid r row hr
        have hlen : 0 < row.core.length := by have := hv.2.1; omega
        let oldMinimum := row.core[0]'hlen
        have hold : row.core.head? = some oldMinimum := by
          simp [List.head?_eq_getElem?, oldMinimum]
        obtain ⟨hmin, hc⟩ := rankRealization_native_replacement_critical h hr hold hn hne (by omega) hi' ht
        have heq := Option.some.inj (hmin.symm.trans hm)
        simpa only [heq] using hc
      · have hj : r < i - sources.length := by omega
        have heq : i - sources.length + sources.length = i := by omega
        have hlookup := native_suffix_rowAt hn hj
        rw [heq, ht] at hlookup
        obtain ⟨old, hold, hv⟩ := Option.map_eq_some_iff.mp hlookup.symm
        subst target
        have hc := (rankRealization_native_suffix_critical h hn hj hold hm (fun _ => embedding r)
          (nativeFreshValues theta (embedding r) r sources)).2
        simpa only [heq, nativeEmbeddingValues] using hc

end FullMarkedBLP

