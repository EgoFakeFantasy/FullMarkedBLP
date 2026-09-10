import FullMarkedBLP.CompletionEdgeExhaustion

namespace FullMarkedBLP

/-- The semantic local interval theorem: all completed edges, not merely the
new packet, are realized. Actual event target-gap identification remains external. -/
theorem rankRealization_completion_all_edges {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r k y p e nextTarget : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (he : row.e = some e) (hey : e ≤ y)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hnt : (row.full r)[k + 1]? = some nextTarget)
    (hs : sources.Nodup) (bounds : ∀ x ∈ sources, x ≤ a.length + 1)
    (gap : y + sources.length < nextTarget) (beforeOwner : y + sources.length < r)
    (packet : ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
      theta (y + 1 + (sources.filter (· < x)).length)) :
    (completeMarkRow row y sources).RealizesEdges (rankOrdinalAction (embedding r)) theta r := by
  have hv := h.valid r row hr
  have hb := (rowAt_bounds hr).2
  obtain ⟨left, right, hl, hrr, sourceGap, hdis, targetGap, belowP, hpy⟩ :=
    rankRealization_completion_geometry h hr hp hk hy hnt bounds gap beforeOwner packet
  have hstep := hv.2.2.2.1
  have hroom := Row.step_lt_length hv.2.2.2
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hstep, hroom.le] using he
  have heb := core_entry_le_owner hv (List.mem_of_getElem? hei)
  have below : ∀ x ∈ sources, x < e := by
    intro x hx
    have hi : (sources.filter (· < x)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
    have heEdge := realizesEdges_e hv (h.edges r row hr) he
    have hlt : theta x < theta e := (rankOrdinalAction_lt_iff (embedding r) _ _).mp (by
      rw [packet x hx, heEdge]
      exact h.increasing _ _ (by omega) (by omega))
    exact (rankRealization_column_lt_iff h (bounds x hx) (by omega)).mp hlt
  have hnew := (rankRealization_completion_core_and_p h hr hp hk hy hnt hs bounds gap beforeOwner packet).1
  apply completeMarkRow_edges_of_all_pairs hv he hey hnew
    (completeMarkRow_e hv he hs hdis targetGap hey below) (h.edges r row hr) packet
  · intro oldIndex x z hox hoz
    have hxc := (full_edge_source_bound hv he hox hoz).1
    by_cases hcore : oldIndex + row.step < row.core.length
    · have hzc : row.core[oldIndex + row.step]? = some z := by
        simpa only [Row.full, List.getElem?_append_left hcore] using hoz
      obtain ⟨j, hjx, hjz⟩ := rankRealization_completion_old_core_pairs h hr hp
        (target_position_after_p hv hk hy hp) (Nat.le_add_left _ _) hzc
        (by simpa using hxc) hs hdis bounds beforeOwner targetGap packet
      exact ⟨j, full_entry_of_core hjx, full_entry_of_core hjz⟩
    · have hlen := (List.getElem?_eq_some_iff.mp hoz).1
      simp only [Row.full, List.length_append, List.length_singleton] at hlen
      have hi : oldIndex + row.step = row.core.length := by omega
      have hix : oldIndex = row.core.length - row.step := by omega
      have hxe : x = e := by
        rw [hix, hei] at hxc
        exact (Option.some.inj hxc).symm
      have hze : z = r + 1 := by simpa [Row.full, hi] using hoz.symm
      rw [hxe, hze]
      exact completeMarkRow_endpoint_pair hv he hey hs hdis targetGap below
  · intro x hx
    obtain ⟨j, hj, hjz, hjx⟩ := completeMarkRow_new_pair hv.1 hs hk hy hl hrr sourceGap
      (fun x hx => lt_of_lt_of_le (below x hx) hey) targetGap hx
    refine ⟨j - (completeMarkRow row y sources).step, full_entry_of_core hjx, ?_⟩
    rw [Nat.sub_add_cancel hj]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (full_entry_of_core (owner := r) hjz)

end FullMarkedBLP

