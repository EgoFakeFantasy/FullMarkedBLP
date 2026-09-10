import FullMarkedBLP.NativeAllEdges

namespace FullMarkedBLP

/-- Exact remaining cardinal obligation for the concrete native columns. -/
theorem rankRealization_native_cardinals_iff {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) :
    (∀ i, i ≤ b.length + 1 → ∃ c : Cardinal.{u}, c.ord =
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length i).val) ↔
    (∀ x ∈ sources, ∃ c : Cardinal.{u}, c.ord = (rankOrdinalAction (embedding r) (theta x)).val) := by
  have hs := native_sources_of_success hn
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  have hrb := (rowAt_bounds hr).2
  have hlen := native_length hn
  constructor
  · intro hc x hx
    have hk : (sources.filter (· < x)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
    have hh := hc (r + 1 + (sources.filter (· < x)).length) (by omega)
    rw [nativeColumnValues_inserted theta _ r sources.length _ hk,
      nativeFreshValues_at_source_rank theta (embedding r) hs hx] at hh
    exact hh
  · intro hc i hi
    by_cases hir : i ≤ r
    · rw [nativeColumnValues_before theta _ hir]
      exact h.cardinals i (by omega)
    · by_cases hit : i ≤ r + sources.length
      · have hk : i - r - 1 < sources.length := by omega
        obtain ⟨x, hx, he⟩ := native_source_rank_surjective hs hk
        have hi' : i = r + 1 + (sources.filter (· < x)).length := by omega
        rw [hi', nativeColumnValues_inserted theta _ r sources.length _ (by omega),
          nativeFreshValues_at_source_rank theta (embedding r) hs hx]
        exact hc x hx
      · simp only [nativeColumnValues, if_neg hir, if_neg hit]
        exact h.cardinals (i - sources.length) (by omega)

end FullMarkedBLP

