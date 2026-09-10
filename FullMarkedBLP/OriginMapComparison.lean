import FullMarkedBLP.EndpointRecordPropagation

namespace FullMarkedBLP

/-- Equal column values identify bounded images of an original index. -/
theorem realized_column_index_eq {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {i j : Nat}
    (hi : i ≤ a.length + 1) (hj : j ≤ a.length + 1) (eq : theta i = theta j) : i = j := by
  by_cases lt : i < j
  · have := h.increasing i j lt hj
    rw [eq] at this
    exact False.elim (lt_irrefl _ this)
  · by_cases gt : j < i
    · have := h.increasing j i gt hi
      rw [eq] at this
      exact False.elim (lt_irrefl _ this)
    · omega

/-- The coherent origin map sends every original bounded index to a bounded current index. -/
theorem origin_map_bounded {initial a : Pattern} {phi : Nat → Nat} {original r j : Nat}
    (mono : StrictMono phi) (maximal : original ≤ initial.length + 1)
    (lengths : initial.length + r = a.length + original)
    (tail : ∀ k, phi (original + k) = r + k) (bound : j ≤ initial.length + 1) :
    phi j ≤ a.length + 1 := by
  have endIndex : original + (initial.length + 1 - original) = initial.length + 1 := by omega
  have endMap := tail (initial.length + 1 - original)
  rw [endIndex] at endMap
  have le := mono.monotone bound
  omega

end FullMarkedBLP
