import FullMarkedBLP.TraceLemmas

namespace FullMarkedBLP

instance (r : Nat) (a : Row) : Decidable (a.CoreValid r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem start_row_index {r : Nat} {row : Row}
    (h : rowAt start r = some row) :
    r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
  have hn : r ≠ 0 := by intro he; subst r; simp [rowAt] at h
  have hb : r ≤ 5 := by
    by_cases hh : r ≤ 5
    · exact hh
    apply False.elim
    have hl : start.length ≤ r - 1 := by simp [start, zero]; omega
    have he : start[r - 1]? = none := List.getElem?_eq_none hl
    simp [rowAt, hn, he] at h
  omega

theorem start_core_valid {r : Nat} {row : Row}
    (h : rowAt start r = some row) : row.CoreValid r := by
  rcases start_row_index h with hr | hr | hr | hr | hr <;>
    subst r <;> simp [rowAt, start, zero] at h <;> subst row <;> decide

theorem start_proper_marks {r : Nat} {row : Row}
    (h : rowAt start r = some row) : row.ProperMarks r := by
  rcases start_row_index h with hr | hr | hr | hr | hr <;>
    subst r <;> simp [rowAt, start, zero] at h <;> subst row
  all_goals simp [Row.ProperMarks]
  exact ⟨3, by decide, by decide⟩

theorem start_sat : Sat start := by
  intro r row h helig
  rcases start_row_index h with hr | hr | hr | hr | hr <;>
    subst r <;> simp [rowAt, start, zero] at h <;> subst row
  · exact ⟨0, 1, ⟨[0, 1], 1, []⟩, 0, by decide⟩
  · simp at helig
  · exact ⟨1, 2, ⟨[0, 1, 2], 1, []⟩, 1, by decide⟩
  · simp at helig
  · exact ⟨3, 4, ⟨[0, 1, 2, 3, 4], 2, [3]⟩, 3, by decide⟩

#print axioms start_core_valid
#print axioms start_proper_marks
#print axioms start_sat

end FullMarkedBLP

