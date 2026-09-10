import FullMarkedBLP.NativeSuffixCritical

namespace FullMarkedBLP

theorem nativeColumnValues_before {alpha : Type u} (old fresh : Nat → alpha)
    {r t x : Nat} (hx : x ≤ r) : nativeColumnValues old fresh r t x = old x := by
  simp only [nativeColumnValues, if_pos hx]

theorem full_entry_le_endpoint {row : Row} {owner k x : Nat}
    (hv : row.CoreValid owner) (hx : (row.full owner)[k]? = some x) : x ≤ owner + 1 := by
  have hm := List.mem_of_getElem? hx
  change x ∈ row.core ++ [owner + 1] at hm
  rcases List.mem_append.mp hm with hc | he
  · have := core_entry_le_owner hv hc
    omega
  · simp only [List.mem_singleton] at he
    omega

theorem rankRealization_native_prefix_edges {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r i : Nat} {row : Row} {sources : List Nat}
    (hn : native a r = some (b, sources)) (hi : i < r) (hr : rowAt a i = some row)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda)
    (freshTheta : Nat → OrdinalDomain lambda) :
    rowAt b i = some row ∧ row.RealizesEdges
      (rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length i))
      (nativeColumnValues theta freshTheta r sources.length) i := by
  constructor
  · exact (native_prefix_rowAt hn hi).trans hr
  · rw [nativeColumnValues_before embedding freshEmbedding (by omega : i ≤ r)]
    intro k x y hx hy
    have hxb := full_entry_le_endpoint (h.valid i row hr) hx
    have hyb := full_entry_le_endpoint (h.valid i row hr) hy
    rw [nativeColumnValues_before theta freshTheta (by omega : x ≤ r),
      nativeColumnValues_before theta freshTheta (by omega : y ≤ r)]
    exact h.edges i row hr k x y hx hy

end FullMarkedBLP

