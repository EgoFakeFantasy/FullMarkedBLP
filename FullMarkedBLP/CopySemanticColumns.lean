import FullMarkedBLP.CopySemanticValues
import FullMarkedBLP.CopyDecomposition
import FullMarkedBLP.RankCardinalPreservation

namespace FullMarkedBLP

theorem shortCopyColumnValues_increasing {lambda : Ordinal.{u}}
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p e : Nat} (copy : shortCopy a = some b)
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p) (he : last.e = some e) :
    ∀ i j, i < j → j ≤ b.length + 1 →
      shortCopyColumnValues theta (embedding a.length) a.length p i <
      shortCopyColumnValues theta (embedding a.length) a.length p j := by
  have hn : a.length ≠ 0 := Nat.ne_of_gt (rowAt_bounds lastAt).1
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg hn, List.getLast?_eq_getElem?] using lastAt
  have valid := h.valid a.length last lastAt
  have hpn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  have hen := fromRight_le_last valid.1 valid.2.2.1 valid.2.2.2.1 he
  have hpe := row_p_lt_e valid hp he
  have length := shortCopy_length copy lastGet hp he
  intro i j hij hj
  by_cases beforeJ : j < a.length
  · rw [shortCopyColumnValues_prefix h lastAt hp (by omega : i ≤ a.length),
      shortCopyColumnValues_prefix h lastAt hp (by omega : j ≤ a.length)]
    exact h.increasing i j hij (by omega)
  · have sourceBound : j - (a.length - p) ≤ e := by omega
    by_cases beforeI : i < a.length
    · rw [shortCopyColumnValues, if_pos beforeI, shortCopyColumnValues, if_neg beforeJ]
      have sourceLe : theta p ≤ theta (j - (a.length - p)) := by
        by_cases same : p = j - (a.length - p)
        · exact (congrArg theta same).le
        · exact (h.increasing p _ (by omega) (by omega)).le
      calc
        theta i < theta a.length := h.increasing i a.length beforeI (by omega)
        _ = rankOrdinalAction (embedding a.length) (theta p) :=
          (realizesEdges_p valid (h.edges a.length last lastAt) hp).symm
        _ ≤ rankOrdinalAction (embedding a.length) (theta (j - (a.length - p))) :=
          rankOrdinalAction_monotone (embedding a.length) sourceLe
    · rw [shortCopyColumnValues, if_neg beforeI, shortCopyColumnValues, if_neg beforeJ]
      apply rankOrdinalAction_strictMono
      exact h.increasing _ _ (by omega) (by omega)

theorem shortCopyColumnValues_cardinals {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p e : Nat} (copy : shortCopy a = some b)
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p) (he : last.e = some e) :
    ∀ i, i ≤ b.length + 1 → ∃ c : Cardinal.{u}, c.ord =
      (shortCopyColumnValues theta (embedding a.length) a.length p i).val := by
  have hn : a.length ≠ 0 := Nat.ne_of_gt (rowAt_bounds lastAt).1
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg hn, List.getLast?_eq_getElem?] using lastAt
  have valid := h.valid a.length last lastAt
  have hpn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  have hen := fromRight_le_last valid.1 valid.2.2.1 valid.2.2.2.1 he
  have hpe := row_p_lt_e valid hp he
  have length := shortCopy_length copy lastGet hp he
  intro i hi
  by_cases before : i < a.length
  · rw [shortCopyColumnValues, if_pos before]
    exact h.cardinals i (by omega)
  · rw [shortCopyColumnValues, if_neg before]
    apply (rankOrdinalAction_cardinal_iff hl (embedding a.length) _).mpr
    exact h.cardinals _ (by omega)

end FullMarkedBLP
