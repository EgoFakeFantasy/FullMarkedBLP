import FullMarkedBLP.RankWordFactors

namespace FullMarkedBLP

theorem rankWord_fixed_of_factors {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (word : List Nat) (c : OrdinalDomain lambda)
    (h : ∀ v ∈ word, rankOrdinalAction (embedding v) c = c) :
    rankOrdinalAction (rankWordEmbedding embedding word) c = c := by
  rw [rankWordEmbedding_ordinalAction]
  induction word with
  | nil => rfl
  | cons v tail ih =>
    simp only [evalWord, ih (fun w hw => h w (by simp [hw])), h v (by simp)]

theorem rankWord_moved_factor {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) {word : List Nat} {c : OrdinalDomain lambda}
    (h : rankOrdinalAction (rankWordEmbedding embedding word) c ≠ c) :
    ∃ v ∈ word, rankOrdinalAction (embedding v) c ≠ c := by
  classical
  by_contra hn
  apply h
  apply rankWord_fixed_of_factors
  intro v hv
  by_contra hm
  exact hn ⟨v, hv, hm⟩

theorem trace_factor_has_row {a : Pattern} {s y v : Nat} {xs : List Nat}
    (ht : Trace a s y xs) (hv : v ∈ xs.dropLast) : ∃ row, rowAt a v = some row := by
  induction ht with
  | stop => simp at hv
  | @next y z tail hsy hp ht ih =>
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons w rest =>
      simp only [List.dropLast_cons_cons, List.mem_cons] at hv
      rcases hv with he | hm
      · subst v
        obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hp
        exact ⟨row, hr⟩
      · exact ih hm

theorem rankRealization_mark_minimum_attained {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r y minimum : Nat} {row : Row}
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) (hm : row.core.head? = some minimum) :
    ∃ xs v factorRow, MarkTrace a r y xs ∧ v ∈ xs.dropLast ∧
      rowAt a v = some factorRow ∧ factorRow.core.head? = some minimum := by
  obtain ⟨xs, delta, hmark, _, hcrit⟩ := rankRealization_mark_word_critical h hr hy hm
  obtain ⟨v, hv, hmove⟩ := rankWord_moved_factor embedding hcrit.1
  have hmarkSaved := hmark
  obtain ⟨old, k, s, _, _, _, _, _, htrace⟩ := hmark
  obtain ⟨factorRow, hf⟩ := trace_factor_has_row htrace hv
  have hvalid := h.valid v factorRow hf
  have hlen : 0 < factorRow.core.length := by have := hvalid.2.1; omega
  let fmin := factorRow.core[0]'hlen
  have hfm : factorRow.core.head? = some fmin := by simp [List.head?_eq_getElem?, fmin]
  have hfc := h.critical v factorRow fmin hf hfm
  have hle := rankWord_critical_le_factor embedding hcrit hv hfc
  have hge := rankCriticalPoint_le_moved hfc hmove
  have he : theta minimum = theta fmin := le_antisymm hle hge
  have hmb := core_entry_le_owner (h.valid r row hr) (List.mem_of_head? hm)
  have hfb := core_entry_le_owner hvalid (List.mem_of_head? hfm)
  have hrb := (rowAt_bounds hr).2
  have hvb := (rowAt_bounds hf).2
  have hidx : minimum = fmin := by
    rcases lt_trichotomy minimum fmin with hlt | heq | hgt
    · have hh := h.increasing minimum fmin hlt (by omega)
      rw [he] at hh
      exact False.elim (lt_irrefl _ hh)
    · exact heq
    · have hh := h.increasing fmin minimum hgt (by omega)
      rw [he] at hh
      exact False.elim (lt_irrefl _ hh)
  exact ⟨xs, v, factorRow, hmarkSaved,
    hv, hf, by simpa only [hidx] using hfm⟩

end FullMarkedBLP


