import FullMarkedBLP.RankMarkedRealization

namespace FullMarkedBLP

/-- Only the finite cardinal columns belonging to the actual pattern are used. -/
theorem rankRealization_trace_cutoff_bounds {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {s y : Nat} {xs : List Nat} {delta : OrdinalDomain lambda}
    (ht : Trace a s y xs)
    (hd : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta) :
    theta y < delta ∧ delta ≤ theta (y + 1) := by
  induction ht generalizing delta with
  | stop => simp [naturalCutoff] at hd
  | @next y z tail hsy hp ht ih =>
    obtain ⟨row, hr, hrp⟩ := Option.bind_eq_some_iff.mp hp
    have hv := h.valid y row hr
    have hybound := (rowAt_bounds hr).2
    have hsucc : theta y < theta (y + 1) := h.increasing y (y + 1) (by omega) (by omega)
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons v rest =>
      cases rest with
      | nil =>
        have he : theta (y + 1) = delta := by simpa [naturalCutoff] using hd
        subst delta
        exact ⟨hsucc, le_rfl⟩
      | cons w rest =>
        obtain ⟨epsilon, he⟩ := naturalCutoff_defined (fun i => rankOrdinalAction (embedding i)) theta
          (word := (v :: w :: rest).dropLast) (by simp)
        simp only [List.dropLast_cons_cons] at he
        have hdelta : rankOrdinalAction (embedding y) epsilon = delta := by
          simpa only [List.dropLast_cons_cons, naturalCutoff, he, Option.map_some, Option.some.injEq] using hd
        have hi := ih he
        have hpimage := realizesEdges_p hv (h.edges y row hr) hrp
        have hroom := Row.step_lt_length hv.2.2.2
        obtain ⟨e, hep⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
        have he' : row.e = some e := hep
        have hze := row_p_lt_e hv hrp he'
        have heowner := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he'
        have htheta : theta (z + 1) ≤ theta e := by
          by_cases heq : z + 1 = e
          · simp only [heq, le_refl]
          · exact le_of_lt (h.increasing (z + 1) e (by omega) (by omega))
        constructor
        · have hh := rankOrdinalAction_strictMono (embedding y) hi.1
          simpa only [hpimage, hdelta] using hh
        · have hh := rankOrdinalAction_monotone (embedding y) (hi.2.trans htheta)
          have heimage := realizesEdges_e hv (h.edges y row hr) he'
          simpa only [heimage, hdelta] using hh

theorem rankRealization_mark_certificate {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r y : Nat} {row : Row}
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) :
    ∃ xs delta, MarkTrace a r y xs ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
      theta y < delta ∧ delta ≤ theta (y + 1) ∧
      rankCutoffAgreement delta.val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  obtain ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hw⟩ := h.marked r row y hr hy
  have hb := rankRealization_trace_cutoff_bounds h ht hd
  exact ⟨xs, delta, ⟨row, k, s, hr, hy, hk, hky, hks, ht⟩, hd, hb.1, hb.2, hw⟩

end FullMarkedBLP



