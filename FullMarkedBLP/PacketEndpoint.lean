import FullMarkedBLP.ScanSat

namespace FullMarkedBLP

theorem row_e_of_p_succ_mem {row : Row} {owner p : Nat}
    (hv : row.CoreValid owner) (hp : row.p = some p) (hm : p + 1 ∈ row.core) :
    row.e = some (p + 1) := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hstep := hv.2.2.2.1
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hstep (by omega)
  have hep : row.e = some e := he
  have hpe := row_p_lt_e hv hp hep
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hei : row.core[row.core.length - (row.step + 1) + 1]? = some e := by
    have hidx : row.core.length - (row.step + 1) + 1 = row.core.length - row.step := by omega
    simpa [fromRight, hstep, show row.step ≤ row.core.length by omega, hidx] using he
  have heq : e = p + 1 := by
    by_cases hh : e = p + 1
    · exact hh
    · have hnot := between_adjacent_not_mem hv.1 hpi hei (by omega : p < p + 1) (by omega : p + 1 < e)
      exact False.elim (hnot hm)
  simpa only [heq] using hep

theorem currentPlusOne_head_endpoint {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s parent child next : Nat} {tail : List Nat}
    (ht : Trace a s parent (parent :: child :: next :: tail))
    (hg : currentPlusOne a (parent :: child :: next :: tail) = true) :
    ∃ row, rowAt a parent = some row ∧ row.p = some child ∧ row.e = some (child + 1) := by
  cases ht with
  | next hsp hpred htail =>
    have hchild := trace_head htail
    simp only [List.head?_cons, Option.some.injEq] at hchild
    subst child
    obtain ⟨row, hr, hp⟩ := Option.bind_eq_some_iff.mp hpred
    rw [currentPlusOne_long_cons] at hg
    have hmem := (Bool.and_eq_true_iff.mp hg).1
    simp only [hr, Option.any_some, List.contains_iff_mem] at hmem
    exact ⟨row, hr, hp, row_e_of_p_succ_mem (valid _ _ hr) hp hmem⟩

theorem scan_packet_head_b_bound {initial a : Pattern} {rec : Records} {cursor : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (reach : ScanReach initial a rec cursor)
    {s parent child next : Nat} {tail : List Nat}
    (ht : Trace a s parent (parent :: child :: next :: tail))
    (hg : currentPlusOne a (parent :: child :: next :: tail) = true)
    (hbefore : parent < cursor)
    (heligible : ∀ row, rowAt a parent = some row → row.core.length ≤ 2 * row.step) :
    ∃ er v, rowAt a (child + 1) = some er ∧ er.b = some v ∧ v ≤ child := by
  obtain ⟨row, hr, hp, he⟩ := currentPlusOne_head_endpoint valid ht hg
  obtain ⟨p, e, er, v, hp', he', her, hb, hle⟩ :=
    scanReach_sat_prefix historyValid reach parent row hbefore hr (heligible row hr)
  have hpeq := Option.some.inj (hp'.symm.trans hp)
  have heeq := Option.some.inj (he'.symm.trans he)
  subst p; subst e
  exact ⟨er, v, her, hb, hle⟩

end FullMarkedBLP


