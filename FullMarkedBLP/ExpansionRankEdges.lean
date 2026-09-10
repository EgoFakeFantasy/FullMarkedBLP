import FullMarkedBLP.ExpansionRankStages

namespace FullMarkedBLP

theorem classify_expansion_data {a : Pattern}
    (h : classify a = .successor ∨ classify a = .limit) :
    ∃ row, a.getLast? = some row ∧ row.core.take 3 = [0, 1, 2] ∧
      (row.core.length = 4 ∨ (row.core.length = 5 ∧ row.step = 3)) := by
  unfold classify at h
  split at h
  next => simp at h
  next =>
    cases last : a.getLast? with
    | none => simp [last] at h
    | some row =>
      simp only [last] at h
      split at h
      next hs => exact ⟨row, rfl, hs.1, Or.inl hs.2⟩
      next =>
        split at h
        next hs => exact ⟨row, rfl, hs.1, Or.inr hs.2⟩
        next => simp at h

/-- Both ordinary expansion row types send the first three columns to
the anchor, current owner column, and implicit terminal column. -/
theorem expansion_row_realizes_three {alpha : Type u} {row : Row} {n : Nat}
    {action : alpha → alpha} {theta : Nat → alpha}
    (valid : row.CoreValid n) (edges : row.RealizesEdges action theta n)
    (first : row.core.take 3 = [0, 1, 2])
    (kind : row.core.length = 4 ∨ (row.core.length = 5 ∧ row.step = 3)) :
    ∃ anchor, row.b = some anchor ∧ 0 < anchor ∧ anchor ≤ n - 1 ∧ 2 < n ∧
      action (theta 0) = theta anchor ∧ action (theta 1) = theta n ∧
      action (theta 2) = theta (n + 1) := by
  have shape := valid.2.2.2
  unfold Row.OrdinaryShape at shape
  have indices : row.core.length = row.step + 2 ∧ 2 ≤ row.step := by omega
  have source0 : row.core[0]? = some 0 := by
    have hh := congrArg (fun xs : List Nat => xs[0]?) first
    simpa using hh
  have source1 : row.core[1]? = some 1 := by
    have hh := congrArg (fun xs : List Nat => xs[1]?) first
    simpa using hh
  have source2 : row.core[2]? = some 2 := by
    have hh := congrArg (fun xs : List Nat => xs[2]?) first
    simpa using hh
  obtain ⟨anchor, hb, positive, bound, size⟩ := coreValid_expansion_bounds valid (by omega)
  have anchorAt : row.core[row.step]? = some anchor := by
    simpa [Row.b, fromRight, indices.1] using hb
  have hp : row.p = some 1 := by
    simpa [Row.p, fromRight, indices.1] using source1
  have he : row.e = some 2 := by
    simpa [Row.e, fromRight, indices.1, show 0 < row.step by omega] using source2
  refine ⟨anchor, hb, positive, bound, size, ?_, realizesEdges_p valid edges hp, realizesEdges_e valid edges he⟩
  exact edges 0 0 anchor (full_entry_of_core source0) (by simpa using full_entry_of_core (owner := n) anchorAt)

/-- Recover the expansion anchor and all three actual ordinal image equations
directly from the parent's literal classification and realized row. -/
theorem rankMarkedRealization_expansion_edges {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding)
    (kind : classify a = .successor ∨ classify a = .limit) :
    ∃ row anchor, a.getLast? = some row ∧ row.b = some anchor ∧
      0 < anchor ∧ anchor ≤ a.length - 1 ∧ 2 < a.length ∧
      rankOrdinalAction (embedding a.length) (theta 0) = theta anchor ∧
      rankOrdinalAction (embedding a.length) (theta 1) = theta a.length ∧
      rankOrdinalAction (embedding a.length) (theta 2) = theta (a.length + 1) := by
  obtain ⟨row, lastGet, first, rowKind⟩ := classify_expansion_data kind
  have lastAt : rowAt a a.length = some row := by
    have hi := lastGet
    rw [List.getLast?_eq_getElem?] at hi
    have hb := (List.getElem?_eq_some_iff.mp hi).1
    simpa only [rowAt, if_neg (by omega : a.length ≠ 0)] using hi
  obtain ⟨anchor, hb, positive, bound, size, image0, image1, image2⟩ :=
    expansion_row_realizes_three (h.valid a.length row lastAt) (h.edges a.length row lastAt) first rowKind
  exact ⟨row, anchor, lastGet, hb, positive, bound, size, image0, image1, image2⟩

end FullMarkedBLP
