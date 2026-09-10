import FullMarkedBLP.RankWordEmbedding

namespace FullMarkedBLP

theorem rankWord_moves_of_factor {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) {word : List Nat} {v : Nat}
    (hv : v ∈ word) {c : OrdinalDomain lambda}
    (hc : rankOrdinalAction (embedding v) c ≠ c) :
    rankOrdinalAction (rankWordEmbedding embedding word) c ≠ c := by
  induction word with
  | nil => simp at hv
  | cons w tail ih =>
    have hlt : c < rankOrdinalAction (rankWordEmbedding embedding (w :: tail)) c := by
      change c < rankOrdinalAction ((embedding w).comp (rankWordEmbedding embedding tail)) c
      rw [rankOrdinalAction_comp]
      rcases List.mem_cons.mp hv with he | ht
      · subst w
        exact (rankOrdinalAction_moved_up (embedding v) hc).trans_le
          (rankOrdinalAction_monotone (embedding v)
            (rankOrdinalAction_le_self_image (rankWordEmbedding embedding tail) c))
      · exact (rankOrdinalAction_moved_up (rankWordEmbedding embedding tail) (ih ht)).trans_le
          (rankOrdinalAction_le_self_image (embedding w) _)
    exact ne_of_gt hlt

theorem rankWord_critical_le_factor {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) {word : List Nat} {v : Nat}
    {c d : OrdinalDomain lambda}
    (hc : RankCriticalPoint (rankWordEmbedding embedding word) c)
    (hv : v ∈ word) (hd : RankCriticalPoint (embedding v) d) : c ≤ d :=
  rankCriticalPoint_le_moved hc (rankWord_moves_of_factor embedding hv hd.1)

theorem rankRealization_mark_factor_minima {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r y minimum : Nat} {row : Row}
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) (hm : row.core.head? = some minimum) :
    ∃ xs, MarkTrace a r y xs ∧ ∀ v ∈ xs.dropLast, ∀ factorRow factorMinimum,
      rowAt a v = some factorRow → factorRow.core.head? = some factorMinimum → minimum ≤ factorMinimum := by
  obtain ⟨xs, delta, ht, _, hc⟩ := rankRealization_mark_word_critical h hr hy hm
  refine ⟨xs, ht, ?_⟩
  intro v hv factorRow factorMinimum hrow hmin
  have hd := h.critical v factorRow factorMinimum hrow hmin
  have hle := rankWord_critical_le_factor embedding hc hv hd
  have hminmem : minimum ∈ row.core := List.mem_of_head? hm
  have hbound := core_entry_le_owner (h.valid r row hr) hminmem
  have hrbound := (rowAt_bounds hr).2
  by_contra hn
  have hlt := h.increasing factorMinimum minimum (by omega) (by omega)
  exact (not_lt_of_ge hle) hlt

end FullMarkedBLP

