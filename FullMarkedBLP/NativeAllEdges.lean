import FullMarkedBLP.NativeReplacementEdges
import FullMarkedBLP.NativeAllCritical

namespace FullMarkedBLP

theorem rankRealization_native_all_edges {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) :
    ∀ i target, rowAt b i = some target → target.RealizesEdges
      (rankOrdinalAction (nativeEmbeddingValues embedding r sources.length i))
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length) i := by
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  by_cases hne : sources = []
  · subst sources
    have heq := Option.some.inj (hn.symm.trans (native_empty hr (native_sources_of_success hn)))
    have hab : b = a := congrArg Prod.fst heq
    subst b
    simp only [List.length_nil, nativeEmbeddingValues, nativeColumnValues_zero]
    exact h.edges
  · have hv := h.valid r row hr
    have hroom := Row.step_lt_length hv.2.2.2
    obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
    obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
    intro i target ht
    by_cases hi : i < r
    · have hold : rowAt a i = some target := (native_prefix_rowAt hn hi).symm.trans ht
      exact (rankRealization_native_prefix_edges h hn hi hold (fun _ => embedding r)
        (nativeFreshValues theta (embedding r) r sources)).2
    · by_cases hi' : i ≤ r + sources.length
      · exact rankRealization_native_replacement_edges h hr hp he hn hne (by omega) hi' ht
      · have hj : r < i - sources.length := by omega
        have heq : i - sources.length + sources.length = i := by omega
        have hlookup := native_suffix_rowAt hn hj
        rw [heq, ht] at hlookup
        obtain ⟨old, hold, hv⟩ := Option.map_eq_some_iff.mp hlookup.symm
        subst target
        have hc := (rankRealization_native_suffix_edges h hn hj hold (fun _ => embedding r)
          (nativeFreshValues theta (embedding r) r sources)).2
        simpa only [heq, nativeEmbeddingValues] using hc

end FullMarkedBLP

