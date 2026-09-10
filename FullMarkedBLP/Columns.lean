import FullMarkedBLP.MarkTrace

namespace FullMarkedBLP

theorem mem_insertColumn (x z : Nat) (xs : List Nat) :
    z ∈ insertColumn x xs ↔ z = x ∨ z ∈ xs := by
  induction xs with
  | nil => simp [insertColumn]
  | cons y ys ih =>
    simp only [insertColumn]
    split
    · simp
    · split
      next he => subst x; simp
      next => simp [ih, or_left_comm]

theorem insertColumn_sorted (x : Nat) {xs : List Nat}
    (hs : xs.Pairwise (· < ·)) : (insertColumn x xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [insertColumn]
  | cons y ys ih =>
    obtain ⟨hy, ht⟩ := List.pairwise_cons.mp hs
    simp only [insertColumn]
    split
    next hxy =>
      apply List.pairwise_cons.mpr
      constructor
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hxy
        · exact Nat.lt_trans hxy (hy z hz)
      · exact hs
    next hxy =>
      split
      · exact hs
      next hne =>
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih ht⟩
        intro z hz
        rcases (mem_insertColumn x z ys).mp hz with rfl | hz
        · omega
        · exact hy z hz

theorem mem_canonicalColumns (z : Nat) (xs : List Nat) :
    z ∈ canonicalColumns xs ↔ z ∈ xs := by
  induction xs with
  | nil => simp [canonicalColumns]
  | cons x xs ih =>
    change z ∈ insertColumn x (canonicalColumns xs) ↔ z ∈ x :: xs
    simp [mem_insertColumn, ih]

theorem canonicalColumns_sorted (xs : List Nat) :
    (canonicalColumns xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [canonicalColumns]
  | cons x xs ih => exact insertColumn_sorted x ih

theorem canonicalColumns_of_sorted {xs : List Nat} (hs : xs.Pairwise (· < ·)) :
    canonicalColumns xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp hs
    change insertColumn x (canonicalColumns xs) = x :: xs
    rw [ih ht]
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hh := hx y (by simp)
      simp [insertColumn, hh]

theorem canonicalColumns_idempotent (xs : List Nat) :
    canonicalColumns (canonicalColumns xs) = canonicalColumns xs :=
  canonicalColumns_of_sorted (canonicalColumns_sorted xs)

end FullMarkedBLP
