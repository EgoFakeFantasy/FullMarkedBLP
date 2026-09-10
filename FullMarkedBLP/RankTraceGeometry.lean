import FullMarkedBLP.RankCutoffBounds
import FullMarkedBLP.RankWordEmbedding

namespace FullMarkedBLP

theorem rankTrace_successor_edge_bound {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (rankOrdinalAction (embedding r)) theta r)
    {y z : Nat} (predecessorAt : predecessor a y = some z) :
    rankOrdinalAction (embedding y) (theta (z + 1)) ≤ theta (y + 1) := by
  obtain ⟨row, rowAtY, hp⟩ := Option.bind_eq_some_iff.mp predecessorAt
  have hv := valid y row rowAtY
  have ownerBound := (rowAt_bounds rowAtY).2
  have room := Row.step_lt_length hv.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
  have hep : row.e = some e := he
  have pBelow := row_p_lt_e hv hp hep
  have eBound := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 hep
  have columns : theta (z + 1) ≤ theta e := by
    by_cases same : z + 1 = e
    · exact (congrArg theta same).le
    · exact (increasing (z + 1) e (by omega) (by omega)).le
  exact (rankOrdinalAction_monotone (embedding y) columns).trans_eq
    (realizesEdges_e hv (edges y row rowAtY) hep)

/-- Natural trace bounds depend on actual row geometry, not on the mark
certificates that are being constructed. -/
theorem rankTrace_cutoff_bounds {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (rankOrdinalAction (embedding r)) theta r)
    {s y : Nat} {xs : List Nat} {delta : OrdinalDomain lambda} (trace : Trace a s y xs)
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta) :
    theta y < delta ∧ delta ≤ theta (y + 1) := by
  induction trace generalizing delta with
  | stop => simp [naturalCutoff] at cutoff
  | @next y z tail sourceLt predecessorAt trace ih =>
    obtain ⟨row, rowAtY, hp⟩ := Option.bind_eq_some_iff.mp predecessorAt
    have ownerBound := (rowAt_bounds rowAtY).2
    cases tail with
    | nil => exact False.elim (trace_nonempty trace rfl)
    | cons v rest =>
      cases rest with
      | nil =>
        have same : theta (y + 1) = delta := by simpa [naturalCutoff] using cutoff
        rw [← same]
        exact ⟨increasing y (y + 1) (by omega) (by omega), le_rfl⟩
      | cons w rest =>
        obtain ⟨epsilon, tailCutoff⟩ := naturalCutoff_defined
          (fun i => rankOrdinalAction (embedding i)) theta (word := (v :: w :: rest).dropLast) (by simp)
        simp only [List.dropLast_cons_cons] at tailCutoff
        have same : rankOrdinalAction (embedding y) epsilon = delta := by
          simpa only [List.dropLast_cons_cons, naturalCutoff, tailCutoff, Option.map_some, Option.some.injEq] using cutoff
        have bounds := ih tailCutoff
        have pImage := realizesEdges_p (valid y row rowAtY) (edges y row rowAtY) hp
        constructor
        · simpa only [pImage, same] using rankOrdinalAction_strictMono (embedding y) bounds.1
        · rw [← same]
          exact (rankOrdinalAction_monotone (embedding y) bounds.2).trans
            (rankTrace_successor_edge_bound valid increasing edges predecessorAt)

theorem rankTrace_eval_successor_le_cutoff {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (rankOrdinalAction (embedding r)) theta r)
    {s y : Nat} {xs : List Nat} {delta : OrdinalDomain lambda} (trace : Trace a s y xs)
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta) :
    rankOrdinalAction (rankWordEmbedding embedding xs.dropLast) (theta (s + 1)) ≤ delta := by
  rw [rankWordEmbedding_ordinalAction]
  induction trace generalizing delta with
  | stop => simp [naturalCutoff] at cutoff
  | @next y z tail sourceLt predecessorAt trace ih =>
    cases tail with
    | nil => exact False.elim (trace_nonempty trace rfl)
    | cons v rest =>
      cases rest with
      | nil =>
        have vz : v = z := by simpa using trace_head trace
        have vs : v = s := by simpa using trace_last trace
        have zs : z = s := vz.symm.trans vs
        have same : theta (y + 1) = delta := by simpa [naturalCutoff] using cutoff
        simpa only [List.dropLast_cons_cons, List.dropLast_singleton, evalWord, ← same, ← zs] using
          rankTrace_successor_edge_bound valid increasing edges predecessorAt
      | cons w rest =>
        obtain ⟨epsilon, tailCutoff⟩ := naturalCutoff_defined
          (fun i => rankOrdinalAction (embedding i)) theta (word := (v :: w :: rest).dropLast) (by simp)
        simp only [List.dropLast_cons_cons] at tailCutoff
        have same : rankOrdinalAction (embedding y) epsilon = delta := by
          simpa only [List.dropLast_cons_cons, naturalCutoff, tailCutoff, Option.map_some, Option.some.injEq] using cutoff
        have bound := rankOrdinalAction_monotone (embedding y) (ih tailCutoff)
        simpa only [List.dropLast_cons_cons, evalWord, same] using bound

end FullMarkedBLP
