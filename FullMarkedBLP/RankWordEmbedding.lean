import FullMarkedBLP.RankCutoffBounds

namespace FullMarkedBLP

def rankWordEmbedding {lambda : Ordinal.{u}} (embedding : Nat → RankElementaryEmbedding lambda) :
    List Nat → RankElementaryEmbedding lambda
  | [] => FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage (RankDomain lambda)
  | v :: tail => (embedding v).comp (rankWordEmbedding embedding tail)

theorem rankWordEmbedding_apply {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (word : List Nat) (x : RankDomain lambda) :
    rankWordEmbedding embedding word x =
      evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) word x := by
  induction word with
  | nil => rfl
  | cons v tail ih => change embedding v (rankWordEmbedding embedding tail x) = _; rw [ih]; rfl

theorem rankWordEmbedding_ordinalAction {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (word : List Nat) (x : OrdinalDomain lambda) :
    rankOrdinalAction (rankWordEmbedding embedding word) x =
      evalWord (fun i => rankOrdinalAction (embedding i)) word x := by
  induction word with
  | nil =>
    apply Subtype.ext
    exact Ordinal.rank_toZFSet x.val
  | cons v tail ih =>
    change rankOrdinalAction ((embedding v).comp (rankWordEmbedding embedding tail)) x = _
    rw [rankOrdinalAction_comp, ih]
    rfl

theorem rankRealization_mark_word_critical {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r y minimum : Nat} {row : Row}
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) (hm : row.core.head? = some minimum) :
    ∃ xs delta, MarkTrace a r y xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      RankCriticalPoint (rankWordEmbedding embedding xs.dropLast) (theta minimum) := by
  obtain ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hw⟩ := h.marked r row y hr hy
  have hb := rankRealization_trace_cutoff_bounds h ht hd
  have hmy := core_head_le_entry (h.valid r row hr) hm hky
  have hyr := (h.proper r row hr).2 y hy
  have hrb := (rowAt_bounds hr).2
  have htheta : theta minimum ≤ theta y := by
    rcases eq_or_lt_of_le hmy with he | he
    · simp only [he, le_refl]
    · exact (h.increasing minimum y he (by omega)).le
  have hvisible : (theta minimum).val < delta.val := htheta.trans_lt hb.1
  have hw' : rankCutoffAgreement delta.val (embedding r) (rankWordEmbedding embedding xs.dropLast) := by
    intro x z hx hz
    simpa only [rankWordEmbedding_apply] using hw x z hx hz
  exact ⟨xs, delta, ⟨row, k, s, hr, hy, hk, hky, hks, ht⟩, hd,
    rankAgreement_transfers_critical hw' (h.critical r row minimum hr hm) hvisible⟩

end FullMarkedBLP

