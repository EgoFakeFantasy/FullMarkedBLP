import FullMarkedBLP.NativeColumnOrder

namespace FullMarkedBLP

theorem row_shift_full_after {row : Row} {r t owner : Nat} (hr : r < owner) :
    (row.shiftAfter r t).full (owner + t) = (row.full owner).map (shiftAfter r t) := by
  simp only [Row.shiftAfter, Row.full, List.map_append, List.map_cons, List.map_nil]
  have he : shiftAfter r t (owner + 1) = owner + t + 1 := by
    unfold shiftAfter
    rw [if_pos (by omega)]
    omega
  rw [he]

theorem row_shift_realizes_edges {alpha : Type u} {row : Row} {r t owner : Nat}
    (old fresh : Nat → alpha) (action : alpha → alpha) (hr : r < owner)
    (h : row.RealizesEdges action old owner) :
    (row.shiftAfter r t).RealizesEdges action (nativeColumnValues old fresh r t) (owner + t) := by
  intro k x y hx hy
  rw [row_shift_full_after hr, List.getElem?_map] at hx hy
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hy
  rw [nativeColumnValues_preserves, nativeColumnValues_preserves]
  exact h k u v hu hv

theorem rankRealization_native_suffix_edges {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r i : Nat} {row : Row} {sources : List Nat}
    (hn : native a r = some (b, sources)) (hi : r < i) (hr : rowAt a i = some row)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda)
    (freshTheta : Nat → OrdinalDomain lambda) :
    rowAt b (i + sources.length) = some (row.shiftAfter r sources.length) ∧
    (row.shiftAfter r sources.length).RealizesEdges
      (rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length (i + sources.length)))
      (nativeColumnValues theta freshTheta r sources.length) (i + sources.length) := by
  constructor
  · rw [native_suffix_rowAt hn hi, hr]
    rfl
  · have he : i + sources.length = shiftAfter r sources.length i := by
      simp only [shiftAfter, if_pos hi]
    rw [he, nativeColumnValues_preserves, ← he]
    exact row_shift_realizes_edges theta freshTheta _ hi (h.edges i row hr)

end FullMarkedBLP

