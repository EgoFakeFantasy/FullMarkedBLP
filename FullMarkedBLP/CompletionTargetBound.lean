import FullMarkedBLP.NativeRecordedMinimum

namespace FullMarkedBLP

theorem target_after_e_of_source_above_minimum {row : Row} {owner minimum k s y e : Nat}
    (hv : row.CoreValid owner) (hm : row.core.head? = some minimum)
    (hk : row.step ≤ k) (hky : row.core[k]? = some y)
    (hks : row.core[k - row.step]? = some s) (hs : minimum < s)
    (he : row.e = some e) : e ≤ y := by
  have hhead : row.core[0]? = some minimum := by simpa [List.head?_eq_getElem?] using hm
  have hpositive : 0 < k - row.step := by
    by_contra hn
    have hz : k - row.step = 0 := by omega
    rw [hz, hhead] at hks
    have heq := Option.some.inj hks
    omega
  have hlength : row.core.length ≤ 2 * row.step + 1 := by
    rcases hv.2.2.2 with ⟨_, hh | hh | hh⟩ <;> omega
  have hroom := Row.step_lt_length hv.2.2.2
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hv.2.2.2.1, show row.step ≤ row.core.length by omega] using he
  have hindex : row.core.length - row.step ≤ k := by omega
  by_cases heq : row.core.length - row.step = k
  · rw [heq, hky] at hei
    exact le_of_eq (Option.some.inj hei).symm
  · obtain ⟨hi, hiv⟩ := List.getElem?_eq_some_iff.mp hei
    obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hky
    have hlt := List.pairwise_iff_getElem.mp hv.1 _ _ hi hj (by omega)
    exact le_of_lt (by simpa only [hiv, hjv] using hlt)

theorem realized_completion_e_le_mark {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y minimum e : Nat} {row : Row} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (h : RankRowRealization a theta embedding)
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) (hm : row.core.head? = some minimum)
    (he : row.e = some e) (hc : completionRecord a rec r y = some sources) : e ≤ y := by
  obtain ⟨k, s, xs, hk, hky, hks, _, hs⟩ :=
    realized_completion_source_above_minimum historyValid reach h hr hy hm hc
  exact target_after_e_of_source_above_minimum (h.valid r row hr) hm hk hky hks hs he

end FullMarkedBLP


