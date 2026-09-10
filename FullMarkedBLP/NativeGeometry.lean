import FullMarkedBLP.Columns

namespace FullMarkedBLP

theorem mem_after_range (r t x : Nat) :
    x ∈ (List.range t).map (fun i => r + 1 + i) ↔ r < x ∧ x ≤ r + t := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h
    exact ⟨x - (r + 1), by omega, by omega⟩

theorem nativeTop_core_mem (row : Row) (r : Nat) (sources : List Nat) (x : Nat) :
    x ∈ (nativeTop row r sources).core ↔
      x ∈ row.core ∨ x ∈ sources ∨ (r < x ∧ x ≤ r + sources.length) := by
  simp [nativeTop, mem_canonicalColumns, mem_after_range]

theorem nativeTop_sorted (row : Row) (r : Nat) (sources : List Nat) :
    (nativeTop row r sources).core.Pairwise (· < ·) ∧
    (nativeTop row r sources).marks.Pairwise (· < ·) :=
  ⟨canonicalColumns_sorted _, canonicalColumns_sorted _⟩

theorem nativeTop_preserves_entries (row : Row) (r : Nat) (sources : List Nat) :
    ∀ x ∈ row.core, x ∈ (nativeTop row r sources).core := by
  intro x hx
  exact (nativeTop_core_mem row r sources x).mpr (Or.inl hx)

theorem nativeTop_marks_before_owner {row : Row} {r : Nat} {sources : List Nat}
    (hmarks : ∀ x ∈ row.marks, x < r) :
    ∀ x ∈ (nativeTop row r sources).marks, x < r + sources.length := by
  intro x hx
  simp only [nativeTop, mem_canonicalColumns, List.mem_filter, List.mem_append,
    List.mem_map, List.mem_range] at hx
  rcases hx.1 with hm | ⟨i, hi, he⟩
  · have := hmarks x hm; omega
  · omega

theorem nativeTop_marks_in_core {row : Row} {r : Nat} {sources : List Nat}
    (hmarks : ∀ x ∈ row.marks, x ∈ row.core) (hr : r ∈ row.core) :
    ∀ x ∈ (nativeTop row r sources).marks, x ∈ (nativeTop row r sources).core := by
  intro x hx
  simp only [nativeTop, mem_canonicalColumns, List.mem_filter, List.mem_append,
    List.mem_map, List.mem_range] at hx
  apply (nativeTop_core_mem row r sources x).mpr
  rcases hx.1 with hm | ⟨i, hi, he⟩
  · exact Or.inl (hmarks x hm)
  · by_cases hz : i = 0
    · have : x = r := by omega
      exact Or.inl (this ▸ hr)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem completeMarkRow_core_mem (row : Row) (y : Nat) (sources : List Nat) (x : Nat) :
    x ∈ (completeMarkRow row y sources).core ↔
      x ∈ row.core ∨ x ∈ sources ∨ (y < x ∧ x ≤ y + sources.length) := by
  simp [completeMarkRow, mem_canonicalColumns, mem_after_range]

theorem completeMarkRow_sorted (row : Row) (y : Nat) (sources : List Nat) :
    (completeMarkRow row y sources).core.Pairwise (· < ·) ∧
    (completeMarkRow row y sources).marks.Pairwise (· < ·) :=
  ⟨canonicalColumns_sorted _, canonicalColumns_sorted _⟩

end FullMarkedBLP
