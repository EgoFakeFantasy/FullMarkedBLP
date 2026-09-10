import FullMarkedBLP.FullRowEdgeSources

namespace FullMarkedBLP

/-- Retained old pairs and inserted pairs exhaust all completed full-row edges;
this includes the implicit endpoint and excludes inserted targets as sources. -/
theorem completeMarkRow_edges_of_all_pairs {alpha : Type u} {action : alpha → alpha}
    {theta : Nat → alpha} {row : Row} {r y e : Nat} {sources : List Nat}
    (hv : row.CoreValid r) (he : row.e = some e) (hey : e ≤ y)
    (hnew : (completeMarkRow row y sources).CoreValid r)
    (henew : (completeMarkRow row y sources).e = some e)
    (oldEdges : row.RealizesEdges action theta r)
    (packet : ∀ x ∈ sources, action (theta x) = theta (y + 1 + (sources.filter (· < x)).length))
    (retained : ∀ i x z, (row.full r)[i]? = some x → (row.full r)[i + row.step]? = some z →
      ∃ j, ((completeMarkRow row y sources).full r)[j]? = some x ∧
        ((completeMarkRow row y sources).full r)[j + (completeMarkRow row y sources).step]? = some z)
    (inserted : ∀ x ∈ sources, ∃ j, ((completeMarkRow row y sources).full r)[j]? = some x ∧
      ((completeMarkRow row y sources).full r)[j + (completeMarkRow row y sources).step]? =
        some (y + 1 + (sources.filter (· < x)).length)) :
    (completeMarkRow row y sources).RealizesEdges action theta r := by
  intro i x z hx hz
  obtain ⟨hxc, hxe⟩ := full_edge_source_bound hnew henew hx hz
  have sorted := coreValid_full_sorted hnew
  have identify : ∀ j v, ((completeMarkRow row y sources).full r)[j]? = some x →
      ((completeMarkRow row y sources).full r)[j + (completeMarkRow row y sources).step]? = some v → z = v := by
    intro j v hj hv
    have hiRank := sorted_rank_at_index sorted hx
    have hjRank := sorted_rank_at_index sorted hj
    have hij : i = j := by omega
    rw [← hij] at hv
    exact Option.some.inj (hz.symm.trans hv)
  rcases (completeMarkRow_core_mem row y sources x).mp (List.mem_of_getElem? hxc) with hold | hsource | htarget
  · obtain ⟨oldIndex, oldTarget, hox, hoz⟩ := full_edge_exists_of_source_le_e hv he hold hxe
    obtain ⟨j, hjx, hjz⟩ := retained oldIndex x oldTarget hox hoz
    rw [identify j oldTarget hjx hjz]
    exact oldEdges oldIndex x oldTarget hox hoz
  · obtain ⟨j, hjx, hjz⟩ := inserted x hsource
    rw [identify j _ hjx hjz]
    exact packet x hsource
  · omega

end FullMarkedBLP

