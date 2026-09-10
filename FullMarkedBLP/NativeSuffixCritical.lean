import FullMarkedBLP.NativeSuffixCertificate

namespace FullMarkedBLP

/-- The minimum of an actual shifted suffix row denotes exactly its old
critical ordinal, including when that minimum itself is shifted. -/
theorem rankRealization_native_suffix_critical {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r i minimum : Nat} {row : Row} {sources : List Nat}
    (hn : native a r = some (b, sources)) (hi : r < i) (hr : rowAt a i = some row)
    (hm : (row.shiftAfter r sources.length).core.head? = some minimum)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda)
    (freshTheta : Nat → OrdinalDomain lambda) :
    rowAt b (i + sources.length) = some (row.shiftAfter r sources.length) ∧
    RankCriticalPoint
      (nativeColumnValues embedding freshEmbedding r sources.length (i + sources.length))
      (nativeColumnValues theta freshTheta r sources.length minimum) := by
  constructor
  · rw [native_suffix_rowAt hn hi, hr]
    rfl
  · change (row.core.map (shiftAfter r sources.length)).head? = some minimum at hm
    rw [List.head?_map] at hm
    obtain ⟨oldMinimum, hold, rfl⟩ := Option.map_eq_some_iff.mp hm
    have hei : i + sources.length = shiftAfter r sources.length i := by
      simp only [shiftAfter, if_pos hi]
    rw [hei, nativeColumnValues_preserves, nativeColumnValues_preserves]
    exact h.critical i row oldMinimum hr hold

end FullMarkedBLP

