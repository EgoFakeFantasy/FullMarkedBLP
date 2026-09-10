import FullMarkedBLP.RealizedEdges

namespace FullMarkedBLP

/-- The successor bound of every factor, transported by precisely its preceding word. -/
def transportedBounds {α : Type u} (action : Nat → α → α) (theta : Nat → α) : List Nat → List α
  | [] => []
  | v :: tail => theta (v + 1) :: (transportedBounds action theta tail).map (action v)

theorem naturalCutoff_minimum {α : Type u}
    (le : α → α → Prop) (action : Nat → α → α) (theta : Nat → α)
    (leRefl : ∀ x, le x x) (leTrans : ∀ {x y z}, le x y → le y z → le x z)
    (mono : ∀ v x y, le x y → le (action v x) (action v y))
    (v : Nat) (tail : List Nat)
    (edges : ∀ parent child, (parent, child) ∈ (v :: tail).zip tail →
      le (action parent (theta (child + 1))) (theta (parent + 1))) :
    ∃ delta, naturalCutoff action theta (v :: tail) = some delta ∧
      delta ∈ transportedBounds action theta (v :: tail) ∧
      ∀ bound ∈ transportedBounds action theta (v :: tail), le delta bound := by
  induction tail generalizing v with
  | nil => exact ⟨theta (v + 1), rfl, by simp [transportedBounds], by simpa [transportedBounds] using leRefl (theta (v + 1))⟩
  | cons w tail ih =>
    obtain ⟨epsilon, he, hem, hleast⟩ := ih w (fun parent child hm => edges parent child (by simp [hm]))
    refine ⟨action v epsilon, by simp [naturalCutoff, he], ?_, ?_⟩
    · simp only [transportedBounds, List.mem_cons, List.mem_map]
      exact Or.inr ⟨epsilon, by simpa [transportedBounds] using hem, rfl⟩
    · intro bound hb
      simp only [transportedBounds, List.mem_cons, List.mem_map] at hb
      rcases hb with hb | ⟨z, hz, hzb⟩
      · subst bound
        have hw := hleast (theta (w + 1)) (by simp [transportedBounds])
        exact leTrans (mono v _ _ hw) (edges v w (by simp))
      · subst bound
        exact mono v _ _ (hleast z (by simpa [transportedBounds] using hz))

/-- The minimum characterization for an actual trace follows from ordinary
    full-row step edges, without requiring the +1 guard. -/
theorem realized_trace_cutoff_minimum {α : Type u} {a : Pattern}
    (le : α → α → Prop) (action : Nat → α → α) (theta : Nat → α)
    (leRefl : ∀ x, le x x) (leTrans : ∀ {x y z}, le x y → le y z → le x z)
    (mono : ∀ v x y, le x y → le (action v x) (action v y))
    (thetaMono : ∀ i j, i ≤ j → le (theta i) (theta j))
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (action r) theta r)
    {s y next : Nat} {tail : List Nat} (ht : Trace a s y (y :: next :: tail)) :
    ∃ delta, naturalCutoff action theta (y :: next :: tail).dropLast = some delta ∧
      delta ∈ transportedBounds action theta (y :: next :: tail).dropLast ∧
      ∀ bound ∈ transportedBounds action theta (y :: next :: tail).dropLast, le delta bound := by
  apply naturalCutoff_minimum le action theta leRefl leTrans mono y (next :: tail).dropLast
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
  have hu := mono parent _ _ (thetaMono (child + 1) e (by omega))
  simpa only [realizesEdges_e hv (edges parent row hr) hep] using hu

theorem transportedBounds_append {α : Type u} (action : Nat → α → α) (theta : Nat → α)
    (front rest : List Nat) :
    transportedBounds action theta (front ++ rest) = transportedBounds action theta front ++
      (transportedBounds action theta rest).map (evalWord action front) := by
  induction front with
  | nil => simp [transportedBounds, evalWord]
  | cons v front ih =>
    simp [transportedBounds, evalWord, ih, List.map_map, Function.comp_def]

theorem transportedBounds_snoc {α : Type u} (action : Nat → α → α) (theta : Nat → α)
    (front : List Nat) (v : Nat) :
    transportedBounds action theta (front ++ [v]) = transportedBounds action theta front ++
      [evalWord action front (theta (v + 1))] := by
  simp [transportedBounds_append, transportedBounds]

end FullMarkedBLP


