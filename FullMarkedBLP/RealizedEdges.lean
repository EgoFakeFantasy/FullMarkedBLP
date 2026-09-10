import FullMarkedBLP.NaturalCutoff

namespace FullMarkedBLP

/-- Only the finite step-edge component of a BLS realization, including the
    implicit endpoint. This does not assert elementarity or critical points. -/
def Row.RealizesEdges {α : Type u} (action : α → α) (theta : Nat → α)
    (owner : Nat) (row : Row) : Prop :=
  ∀ i x y, (row.full owner)[i]? = some x →
    (row.full owner)[i + row.step]? = some y → action (theta x) = theta y

theorem full_entry_of_core {row : Row} {owner i x : Nat}
    (h : row.core[i]? = some x) : (row.full owner)[i]? = some x := by
  have hi := (List.getElem?_eq_some_iff.mp h).1
  simpa only [Row.full, List.getElem?_append_left hi] using h

theorem realizesEdges_p {α : Type u} {action : α → α} {theta : Nat → α}
    {owner p : Nat} {row : Row} (hv : row.CoreValid owner)
    (hedges : row.RealizesEdges action theta owner) (hp : row.p = some p) :
    action (theta p) = theta owner := by
  have hstep := hv.2.2.2.1
  have hlen := Row.step_lt_length hv.2.2.2
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hlast := hv.2.2.1
  rw [List.getLast?_eq_getElem?] at hlast
  apply hedges (row.core.length - (row.step + 1)) p owner (full_entry_of_core hpi)
  have heq : row.core.length - (row.step + 1) + row.step = row.core.length - 1 := by omega
  simpa only [heq] using (full_entry_of_core (owner := owner) hlast)

theorem realizesEdges_e {α : Type u} {action : α → α} {theta : Nat → α}
    {owner e : Nat} {row : Row} (hv : row.CoreValid owner)
    (hedges : row.RealizesEdges action theta owner) (he : row.e = some e) :
    action (theta e) = theta (owner + 1) := by
  have hstep := hv.2.2.2.1
  have hlen := Row.step_lt_length hv.2.2.2
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hstep, show row.step ≤ row.core.length by omega] using he
  apply hedges (row.core.length - row.step) e (owner + 1) (full_entry_of_core hei)
  have heq : row.core.length - row.step + row.step = row.core.length := by omega
  simp [heq, Row.full]

theorem guarded_trace_cutoff_exact {α : Type u} {a : Pattern}
    (action : Nat → α → α) (theta : Nat → α)
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (action r) theta r)
    {s y next : Nat} {tail : List Nat}
    (ht : Trace a s y (y :: next :: tail))
    (hg : currentPlusOne a (y :: next :: tail) = true) :
    naturalCutoff action theta (y :: next :: tail).dropLast = some (theta (y + 1)) := by
  simp only [List.dropLast_cons_cons]
  apply naturalCutoff_exact_of_successor_edges
  intro parent child hm
  have hm' : (parent, child) ∈ (y :: next :: tail).dropLast.zip (y :: next :: tail).dropLast.tail := by
    simpa only [List.dropLast_cons_cons, List.tail_cons] using hm
  obtain ⟨row, hr, _, he⟩ := currentPlusOne_all_endpoints valid ht hg parent child hm'
  exact realizesEdges_e (valid parent row hr) (edges parent row hr) he

theorem realized_trace_cutoff_bounds {α : Type u} {a : Pattern}
    (lt le : α → α → Prop) (action : Nat → α → α) (theta : Nat → α)
    (leRefl : ∀ x, le x x) (leTrans : ∀ {x y z}, le x y → le y z → le x z)
    (strict : ∀ v x y, lt x y → lt (action v x) (action v y))
    (mono : ∀ v x y, le x y → le (action v x) (action v y))
    (thetaMono : ∀ i j, i ≤ j → le (theta i) (theta j))
    (thetaSucc : ∀ v, lt (theta v) (theta (v + 1)))
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (action r) theta r)
    {s y next : Nat} {tail : List Nat} {delta : α}
    (ht : Trace a s y (y :: next :: tail))
    (hd : naturalCutoff action theta (y :: next :: tail).dropLast = some delta) :
    lt (theta y) delta ∧ le delta (theta (y + 1)) := by
  apply naturalCutoff_bounds lt le action theta leRefl leTrans strict mono thetaSucc
    y (next :: tail).dropLast ?_ hd
  intro parent child hm
  have hm' : (parent, child) ∈ (y :: next :: tail).dropLast.zip (y :: next :: tail).dropLast.tail := by
    simpa only [List.dropLast_cons_cons, List.tail_cons] using hm
  have hp := trace_internal_predecessors ht parent child hm'
  obtain ⟨row, hr, hrp⟩ := Option.bind_eq_some_iff.mp hp
  have hv := valid parent row hr
  have hroom := Row.step_lt_length hv.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
  have hep : row.e = some e := he
  have hpe := row_p_lt_e hv hrp hep
  refine ⟨realizesEdges_p hv (edges parent row hr) hrp, ?_⟩
  have hu := mono parent _ _ (thetaMono (child + 1) e (by omega))
  simpa only [realizesEdges_e hv (edges parent row hr) hep] using hu

end FullMarkedBLP

