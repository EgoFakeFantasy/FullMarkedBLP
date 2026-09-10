import FullMarkedBLP.CopyCore

namespace FullMarkedBLP

theorem MapsEntries.dropLast {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : MapsEntries f xs ys) : MapsEntries f xs.dropLast ys.dropLast := by
  induction h with
  | nil => exact MapsEntries.nil
  | @cons x y xs ys hx ht ih =>
    cases ht with
    | nil => exact MapsEntries.nil
    | cons hz tail => simpa only [List.dropLast_cons_cons] using MapsEntries.cons hx ih

theorem MapsEntries.last {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : MapsEntries f xs ys) {x : α} (hx : xs.getLast? = some x) :
    ∃ y, ys.getLast? = some y ∧ f x = some y := by
  induction h with
  | nil => simp at hx
  | @cons u v us vs hu ht ih =>
    cases ht with
    | nil =>
      have he : u = x := by simpa using hx
      subst x
      exact ⟨v, rfl, hu⟩
    | cons hw tail =>
      obtain ⟨y, hy, hf⟩ := ih (by simpa using hx)
      exact ⟨y, by simpa using hy, hf⟩

theorem copiedCore_maps_entries {n source : Nat} {last row : Row} {core : List Nat}
    (h : copiedCore n last source row = some core) : MapsEntries (copyEntry n last) row.core core := by
  obtain ⟨full, hf, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  have hm := (option_mapM_forall2 hf).dropLast
  simpa [Row.full] using hm

theorem copiedCore_owner {n source : Nat} {last row : Row} {core : List Nat}
    (hr : row.CoreValid source) (h : copiedCore n last source row = some core) :
    ∃ owner, core.getLast? = some owner ∧ copyEntry n last source = some owner :=
  (copiedCore_maps_entries h).last hr.2.2.1

theorem copiedRow_coreValid {a : Pattern} {last row copied : Row} {source : Nat}
    (hv : last.CoreValid a.length) (hr : row.CoreValid source)
    (h : copiedRow a last source row = some copied) :
    ∃ owner, copyEntry a.length last source = some owner ∧ copied.CoreValid owner := by
  have hshape := copiedRow_shape hr.2.2.2 h
  obtain ⟨core, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  obtain ⟨owner, ho, hm⟩ := copiedCore_owner hr hc
  have hl := copiedCore_length hc
  have hmin := hr.2.1
  exact ⟨owner, hm, copiedCore_sorted hv hr hc, by simpa only [hl] using hmin, ho, hshape⟩

end FullMarkedBLP

