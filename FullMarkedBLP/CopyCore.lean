import FullMarkedBLP.CopyStrict

namespace FullMarkedBLP

inductive MapsEntries {α β : Type} (f : α → Option β) : List α → List β → Prop
  | nil : MapsEntries f [] []
  | cons {x y xs ys} : f x = some y → MapsEntries f xs ys → MapsEntries f (x :: xs) (y :: ys)

theorem MapsEntries.length_eq {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : MapsEntries f xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

theorem MapsEntries.mem_right {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : MapsEntries f xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, f x = some y := by
  induction h with
  | nil => simp at hy
  | @cons x z xs ys hx ht ih =>
    rcases List.mem_cons.mp hy with he | he
    · subst z; exact ⟨x, by simp, hx⟩
    · obtain ⟨w, hw, hv⟩ := ih he
      exact ⟨w, List.mem_cons_of_mem x hw, hv⟩
theorem option_mapM_forall2 {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : MapsEntries f xs ys := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := by simpa using h.symm
    subst ys
    exact MapsEntries.nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, ht, h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    exact MapsEntries.cons hy (ih ht)

theorem option_mapM_length {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length :=
  (option_mapM_forall2 h).length_eq.symm

theorem copy_mapM_sorted {n : Nat} {last : Row} {xs ys : List Nat}
    (hv : last.CoreValid n) (hs : xs.Pairwise (· < ·))
    (h : xs.mapM (copyEntry n last) = some ys) : ys.Pairwise (· < ·) := by
  have hf := option_mapM_forall2 h
  clear h
  induction hf with
  | nil => exact List.Pairwise.nil
  | @cons x y xs ys hx ht ih =>
    have hs' := List.pairwise_cons.mp hs
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hs'.2⟩
    intro z hz
    obtain ⟨w, hw, hmap⟩ := ht.mem_right hz
    exact copyEntry_strict hv (hs'.1 w hw) hx hmap

theorem copiedCore_length {n source : Nat} {last row : Row} {core : List Nat}
    (h : copiedCore n last source row = some core) : core.length = row.core.length := by
  obtain ⟨full, hf, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  have hl := option_mapM_length hf
  simp only [Row.full, List.length_append, List.length_singleton] at hl
  simp only [List.length_dropLast]
  omega

theorem copiedCore_sorted {n source : Nat} {last row : Row} {core : List Nat}
    (hv : last.CoreValid n) (hr : row.CoreValid source)
    (h : copiedCore n last source row = some core) : core.Pairwise (· < ·) := by
  obtain ⟨full, hf, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  have hs : (row.full source).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hr.1, by simp, ?_⟩
    intro x hx y hy
    have he : y = source + 1 := by simpa using hy
    have hb := core_entry_le_owner hr hx
    omega
  exact (copy_mapM_sorted hv hs hf).sublist (List.dropLast_sublist _)

theorem copiedRow_shape {a : Pattern} {last row copied : Row} {source : Nat}
    (hv : row.OrdinaryShape) (h : copiedRow a last source row = some copied) : copied.OrdinaryShape := by
  obtain ⟨core, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  have hl := copiedCore_length hc
  simpa only [Row.OrdinaryShape, hl] using hv

end FullMarkedBLP



