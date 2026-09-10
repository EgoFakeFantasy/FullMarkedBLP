import FullMarkedBLP.NativePrefixCertificate

namespace FullMarkedBLP

theorem rankRealization_native_prefix_critical {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r i minimum : Nat} {row : Row} {sources : List Nat}
    (hn : native a r = some (b, sources)) (hi : i < r) (hr : rowAt a i = some row)
    (hm : row.core.head? = some minimum)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda)
    (freshTheta : Nat → OrdinalDomain lambda) :
    rowAt b i = some row ∧
    RankCriticalPoint (nativeColumnValues embedding freshEmbedding r sources.length i)
      (nativeColumnValues theta freshTheta r sources.length minimum) := by
  constructor
  · exact (native_prefix_rowAt hn hi).trans hr
  · have hmin := core_entry_le_owner (h.valid i row hr) (List.mem_of_head? hm)
    rw [nativeColumnValues_before embedding freshEmbedding (by omega : i ≤ r),
      nativeColumnValues_before theta freshTheta (by omega : minimum ≤ r)]
    exact h.critical i row minimum hr hm

end FullMarkedBLP

