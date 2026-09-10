import FullMarkedBLP.CopyOwner
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Induction

namespace FullMarkedBLP

/-- A decreasing list formed from the upper entries and entries below the
omitted minimum is lexicographically smaller than the original list. -/
theorem descending_lex_lt_append_minimum {xs ys : List Nat} {minimum : Nat}
    (hx : xs.Pairwise (· > ·)) (hy : ys.Pairwise (· > ·))
    (allowed : ∀ x ∈ xs, x < minimum ∨ x ∈ ys)
    (above : ∀ y ∈ ys, minimum < y) :
    xs < ys ++ [minimum] := by
  induction ys generalizing xs with
  | nil =>
    cases xs with
    | nil => exact List.Lex.nil
    | cons x xs =>
      exact List.Lex.rel ((allowed x (by simp)).resolve_right (by simp))
  | cons y ys ih =>
    cases xs with
    | nil => exact List.Lex.nil
    | cons x xs =>
      have hx' := List.pairwise_cons.mp hx
      have hy' := List.pairwise_cons.mp hy
      have hmy := above y (by simp)
      have hxy : x ≤ y := by
        rcases allowed x (by simp) with low | mem
        · omega
        · rcases List.mem_cons.mp mem with rfl | mem
          · exact le_rfl
          · exact (hy'.1 x mem).le
      rcases lt_or_eq_of_le hxy with lt | rfl
      · exact List.Lex.rel lt
      · apply List.Lex.cons
        apply ih hx'.2 hy'.2
        · intro z hz
          rcases allowed z (by simp [hz]) with low | mem
          · exact Or.inl low
          · apply Or.inr
            rcases List.mem_cons.mp mem with eq | mem
            · have := hx'.1 z hz
              omega
            · exact mem
        · exact fun z hz => above z (by simp [hz])

theorem Row.shortKey_mem_core {row : Row} {x : Nat} (h : x ∈ row.shortKey) :
    x ∈ row.core := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_of_mem_drop (List.mem_reverse.mp h)
  · exact List.mem_of_mem_take h

theorem Row.shortKey_eq_of_head {row : Row} {minimum : Nat}
    (h : row.core.head? = some minimum) :
    row.shortKey = (row.core.drop row.step).reverse ++ [minimum] := by
  cases hc : row.core with
  | nil => simp [hc] at h
  | cons x xs =>
    have eq : x = minimum := by simpa [hc] using h
    simp [Row.shortKey, hc, eq]

theorem Row.minimum_lt_drop {row : Row} {minimum x : Nat}
    (sorted : row.core.Pairwise (· < ·)) (positive : 0 < row.step)
    (hm : row.core.head? = some minimum) (hx : x ∈ row.core.drop row.step) :
    minimum < x := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  have hib : row.step + i < row.core.length := by
    simp only [List.length_drop] at hi
    omega
  have h0 : 0 < row.core.length := by omega
  have hfirst : row.core[0] = minimum := by
    exact (List.getElem?_eq_some_iff.mp (by simpa only [List.head?_eq_getElem?] using hm)).2
  have hvalue : row.core[row.step + i] = x := by
    simpa only [List.getElem_drop] using he
  have := List.pairwise_iff_getElem.mp sorted 0 (row.step + i) h0 hib (by omega)
  omega

theorem Row.shortKey_decreasing {row : Row}
    (sorted : row.core.Pairwise (· < ·)) (positive : 0 < row.step) :
    row.shortKey.Pairwise (· > ·) := by
  cases hm : row.core.head? with
  | none =>
    have empty : row.core = [] := List.head?_eq_none_iff.mp hm
    simp [Row.shortKey, empty]
  | some minimum =>
    rw [row.shortKey_eq_of_head hm]
    apply List.pairwise_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · exact List.pairwise_reverse.mpr (sorted.sublist (List.drop_sublist _ _))
    · intro x hx y hy
      have eq : y = minimum := by simpa using hy
      subst y
      exact Row.minimum_lt_drop sorted positive hm (List.mem_reverse.mp hx)

theorem row_shortKey_lt_of_allowed {row last : Row} {minimum : Nat}
    (sorted : row.core.Pairwise (· < ·)) (positive : 0 < row.step)
    (lastSorted : last.core.Pairwise (· < ·)) (lastPositive : 0 < last.step)
    (hm : last.core.head? = some minimum)
    (allowed : ∀ x ∈ row.shortKey, x < minimum ∨ x ∈ last.core.drop last.step) :
    row.shortKey < last.shortKey := by
  rw [last.shortKey_eq_of_head hm]
  apply descending_lex_lt_append_minimum (Row.shortKey_decreasing sorted positive)
    (List.pairwise_reverse.mpr (lastSorted.sublist (List.drop_sublist _ _)))
  · intro x hx
    exact (allowed x hx).imp_right List.mem_reverse.mpr
  · intro x hx
    exact Row.minimum_lt_drop lastSorted lastPositive hm (List.mem_reverse.mp hx)

theorem Row.shortKey_head {row : Row} {owner : Nat} (valid : row.CoreValid owner) :
    row.shortKey.head? = some owner := by
  have bound := Row.step_lt_length valid.2.2.2
  simp only [Row.shortKey, List.head?_append, List.head?_reverse, List.getLast?_drop,
    show ¬row.core.length ≤ row.step by omega, if_false, valid.2.2.1]
  rfl

theorem Row.shortKey_two_high {row : Row} {owner anchor : Nat}
    (valid : row.CoreValid owner) (len : row.core.length = row.step + 2)
    (hb : row.b = some anchor) :
    row.shortKey = owner :: anchor :: row.core.take 1 := by
  have first : row.core[row.step]? = some anchor := by
    simpa [Row.b, fromRight, len] using hb
  have second : row.core[row.step + 1]? = some owner := by
    simpa [List.getLast?_eq_getElem?, len] using valid.2.2.1
  have dropped : row.core.drop row.step = [anchor, owner] := by
    apply List.ext_getElem (by simp [len])
    intro i hi hj
    have bound : i < 2 := by simpa using hj
    have entry : (row.core.drop row.step)[i]? = ([anchor, owner] : List Nat)[i]? := by
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · simpa using first
      · simpa using second
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.some.injEq] using entry
  simp [Row.shortKey, dropped]

theorem shortKey_lt_of_prefix_first_row {initial rest : Pattern} {row last : Row}
    (h : row.shortKey < last.shortKey) :
    shortKey (initial ++ row :: rest) < shortKey (initial ++ [last]) := by
  simp only [shortKey, List.map_append, List.map_cons, List.map_nil]
  exact List.Lex.append_left _ (List.Lex.rel h) _

theorem shortKey_lt_of_cut_prefix {a b : Pattern} {row last : Row}
    (hl : a.getLast? = some last) (initial : a.dropLast <+: b)
    (hr : rowAt b a.length = some row) (h : row.shortKey < last.shortKey) :
    shortKey b < shortKey a := by
  obtain ⟨old, eq⟩ := List.getLast?_eq_some_iff.mp hl
  subst a
  simp only [List.dropLast_concat] at initial
  obtain ⟨rest, eq⟩ := initial
  subst b
  have entry : rest[0]? = some row := by
    simpa [rowAt, List.getElem?_append_right] using hr
  obtain ⟨tail, eq⟩ := List.head?_eq_some_iff.mp (by simpa only [List.head?_eq_getElem?] using entry)
  subst rest
  exact shortKey_lt_of_prefix_first_row h

theorem cut_shortKey_lt {a b : Pattern} (h : cut a = some b) :
    shortKey b < shortKey a := by
  unfold cut at h
  split at h
  next hn =>
    cases Option.some.inj h
    induction a using List.reverseRecOn with
    | nil => simp at hn
    | append_singleton a row ih =>
      simp only [List.dropLast_concat, shortKey, List.map_append, List.map_cons, List.map_nil]
      simpa only [List.append_nil] using
        List.Lex.append_left (fun x y : List Nat => x < y)
          (show List.Lex (· < ·) [] [row.shortKey] from .nil) (a.map Row.shortKey)
  next => simp at h

end FullMarkedBLP
