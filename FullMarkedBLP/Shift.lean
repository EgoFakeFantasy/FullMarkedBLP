import FullMarkedBLP.NativeBlockActual

namespace FullMarkedBLP

theorem shiftAfter_strict (r t : Nat) {x y : Nat} (h : x < y) :
    shiftAfter r t x < shiftAfter r t y := by
  unfold shiftAfter
  split <;> split <;> omega

theorem shiftAfter_sorted (r t : Nat) {xs : List Nat} (h : xs.Pairwise (· < ·)) :
    (xs.map (shiftAfter r t)).Pairwise (· < ·) := by
  apply List.pairwise_map.mpr
  exact h.imp (shiftAfter_strict r t)

theorem row_shift_coreValid {row : Row} {owner r t : Nat}
    (h : row.CoreValid owner) :
    (row.shiftAfter r t).CoreValid (shiftAfter r t owner) := by
  refine ⟨shiftAfter_sorted r t h.1, ?_, ?_, ?_⟩
  · simpa [Row.shiftAfter] using h.2.1
  · simp [Row.shiftAfter, h.2.2.1]
  · simpa [Row.shiftAfter, Row.OrdinaryShape] using h.2.2.2

theorem row_shift_properMarks {row : Row} {owner r t : Nat}
    (h : row.ProperMarks owner) :
    (row.shiftAfter r t).ProperMarks (shiftAfter r t owner) := by
  refine ⟨shiftAfter_sorted r t h.1, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hb, k, hk, he⟩ := h.2 x hx
  refine ⟨shiftAfter_strict r t hb, k, hk, ?_⟩
  simp [Row.shiftAfter, he]

#print axioms row_shift_coreValid
#print axioms row_shift_properMarks
end FullMarkedBLP

