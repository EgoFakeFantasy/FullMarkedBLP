import FullMarkedBLP.CompletionActualCritical

namespace FullMarkedBLP

theorem row_e_eq_successor_of_mem {row : Row} {r p e : Nat}
    (hv : row.CoreValid r) (hp : row.p = some p) (he : row.e = some e)
    (hm : p + 1 ∈ row.core) : e = p + 1 := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hei : row.core[row.core.length - (row.step + 1) + 1]? = some e := by
    have hi : row.core.length - (row.step + 1) + 1 = row.core.length - row.step := by omega
    simpa [Row.e, fromRight, hv.2.2.2.1, hroom.le, hi] using he
  have hpe := row_p_lt_e hv hp he
  by_contra hne
  exact between_adjacent_not_mem hv.1 hpi hei (by omega) (by omega) hm

theorem realized_successor_edge {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r p : Nat} {row : Row}
    (hr : rowAt a r = some row) (hp : row.p = some p) (hm : p + 1 ∈ row.core) :
    rankOrdinalAction (embedding r) (theta (p + 1)) = theta (r + 1) := by
  have hv := h.valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 hroom.le
  have heq := row_e_eq_successor_of_mem hv hp he hm
  exact realizesEdges_e hv (h.edges r row hr) (by simpa only [heq] using he)

end FullMarkedBLP
