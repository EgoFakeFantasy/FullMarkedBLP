import FullMarkedBLP.FrozenPredecessorGeometry

namespace FullMarkedBLP

/-- Assemble the row realization after one completion event. Event geometry
preserves the core and predecessors; the caller supplies the independently
proved edge and marked-word certificates. This common assembly applies to
entrance events, intermediate direct events, and arbitrary-word copy events. -/
theorem completionEvent_realization {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat} (event : CompletionEventGeometry a rec r y theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (edges : ∀ i out, rowAt (completeMark a rec r y) i = some out →
      out.RealizesEdges (rankOrdinalAction (embedding i)) theta i)
    (certificates : ∀ out, rowAt (completeMark a rec r y) r = some out → ∀ z ∈ out.marks,
      ∃ xs delta, MarkTrace (completeMark a rec r y) r z xs ∧
        naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta ∧
        rankCutoffAgreement delta.val (embedding r)
          (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast)) :
    RankRowRealization (completeMark a rec r y) theta embedding := by
  have h := event.1
  have valid := completionEvent_coreValid event
  have pred := completionEvent_preserves_predecessors event
  cases hc : completionRecord a rec r y with
  | none => simpa only [completeMark, hr, hc] using h
  | some sources =>
    obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
      event.2 row sources hr hc
    have hlen : 0 < row.core.length := by have := (h.valid r row hr).2.1; omega
    let minimum := row.core[0]'hlen
    have hmin : row.core.head? = some minimum := by simp [List.head?_eq_getElem?, minimum]
    obtain ⟨proper, minimumEq, critical⟩ := rankRealization_completion_marks_critical h hr hp hm hmin
      hk hy hnext hs bounds gap beforeOwner packet
    simp only [completeMark, hr, hc] at valid edges certificates pred ⊢
    refine ⟨valid, ?_, ?_, ?_, edges, ?_, ?_⟩
    · intro i out hout
      by_cases hi : i = r
      · subst i
        rw [rowAt_set_self hr] at hout
        cases Option.some.inj hout
        exact proper
      · rw [rowAt_set_other hr hi] at hout
        exact h.proper i out hout
    · intro i j hij hj
      exact h.increasing i j hij (by simpa only [List.length_set] using hj)
    · intro i hi
      exact h.cardinals i (by simpa only [List.length_set] using hi)
    · intro i out low hout hlow
      by_cases hi : i = r
      · subst i
        rw [rowAt_set_self hr] at hout
        cases Option.some.inj hout
        have eq := Option.some.inj (minimumEq.symm.trans hlow)
        subst low
        exact critical
      · rw [rowAt_set_other hr hi] at hout
        exact h.critical i out low hout hlow
    · intro i out z hout hz
      by_cases hi : i = r
      · subst i
        obtain ⟨xs, delta, mark, cutoff, agreement⟩ := certificates out hout z hz
        obtain ⟨actual, j, source, hactual, _, hj, hzy, hsource, trace⟩ := mark
        have eq := Option.some.inj (hactual.symm.trans hout)
        subst actual
        exact ⟨j, source, xs, delta, hj, hzy, hsource, trace, cutoff, agreement⟩
      · have old := hout
        rw [rowAt_set_other hr hi] at old
        obtain ⟨j, source, xs, delta, hj, hzy, hsource, trace, cutoff, agreement⟩ := h.marked i out z old hz
        refine ⟨j, source, xs, delta, hj, hzy, hsource, ?_, cutoff, agreement⟩
        have moved := trace_map (b := a.set (r - 1) (completeMarkRow row y sources))
          id (fun hlt => hlt) trace (by
            intro x w _ hw
            simpa only [id_eq, pred x] using hw)
        simpa only [List.map_id, id_eq] using moved

end FullMarkedBLP
