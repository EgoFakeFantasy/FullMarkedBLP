import FullMarkedBLP.CompletionTrace

namespace FullMarkedBLP

theorem completeMarkRow_rank_bound {row : Row} {y z : Nat} {sources : List Nat}
    (hc : row.core.Nodup) (hs : sources.Nodup)
    (hdis : ∀ x ∈ sources, x ∉ row.core) (hbelow : ∀ x ∈ sources, x < z) :
    (row.core.filter (· < z)).length + sources.length ≤
      ((completeMarkRow row y sources).core.filter (· < z)).length := by
  have hn : (row.core.filter (· < z) ++ sources).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hc.sublist List.filter_sublist, hs, ?_⟩
    intro x hx w hw he
    subst w
    exact hdis x hw (List.mem_filter.mp hx).1
  have hsub : ∀ x ∈ row.core.filter (· < z) ++ sources,
      x ∈ (completeMarkRow row y sources).core.filter (· < z) := by
    intro x hx
    apply List.mem_filter.mpr
    rcases List.mem_append.mp hx with hx | hx
    · have hh := List.mem_filter.mp hx
      exact ⟨(completeMarkRow_core_mem row y sources x).mpr (Or.inl hh.1), hh.2⟩
    · exact ⟨(completeMarkRow_core_mem row y sources x).mpr (Or.inr (Or.inl hx)),
        by simpa using hbelow x hx⟩
  simpa only [List.length_append] using nodup_subset_length hn hsub

theorem completeMarkRow_target_position {row : Row} {y z k : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hdis : ∀ x ∈ sources, x ∉ row.core) (hbelow : ∀ x ∈ sources, x < z)
    (hk : row.step ≤ k) (hky : row.core[k]? = some y) (hyz : y ≤ z)
    (hzm : z ∈ (completeMarkRow row y sources).core) :
    ∃ j, (completeMarkRow row y sources).step ≤ j ∧
      (completeMarkRow row y sources).core[j]? = some z := by
  have hn := hc.imp (fun h => Nat.ne_of_lt h)
  have hmono : (row.core.filter (· < y)).length ≤ (row.core.filter (· < z)).length := by
    apply nodup_subset_length (hn.sublist List.filter_sublist)
    intro x hx
    obtain ⟨hm, hb⟩ := List.mem_filter.mp hx
    exact List.mem_filter.mpr ⟨hm, by simp at hb ⊢; omega⟩
  have hrank := sorted_rank_at_index hc hky
  have hb := completeMarkRow_rank_bound (y := y) hn hs hdis hbelow
  apply (target_position_iff_rank (completeMarkRow_sorted row y sources).1 hzm).mpr
  change row.step + sources.length ≤ _
  omega

theorem completeMarkRow_properMarks {row : Row} {owner y : Nat} {sources : List Nat}
    (hv : row.CoreValid owner) (hm : row.ProperMarks owner) (hy : y ∈ row.marks)
    (hs : sources.Nodup) (hdis : ∀ x ∈ sources, x ∉ row.core)
    (hbefore : ∀ x ∈ sources, ∀ z ∈ row.marks, x < z)
    (hbound : y + sources.length < owner) :
    (completeMarkRow row y sources).ProperMarks owner := by
  refine ⟨(completeMarkRow_sorted row y sources).2, ?_⟩
  intro z hz
  simp only [completeMarkRow, mem_canonicalColumns, List.mem_append] at hz
  rcases hz with hold | hnew
  · have hzm := (List.mem_filter.mp hold).1
    obtain ⟨hb, k, hk, hky⟩ := hm.2 z hzm
    refine ⟨hb, ?_⟩
    have hc := hv.1.imp (fun h => Nat.ne_of_lt h)
    have hlow := completeMarkRow_rank_bound (y := y) hc hs hdis (fun x hx => hbefore x hx z hzm)
    have hrank := sorted_rank_at_index hv.1 hky
    have hmem := (completeMarkRow_core_mem row y sources z).mpr
      (Or.inl (List.mem_iff_getElem?.mpr ⟨k, hky⟩))
    apply (target_position_iff_rank (completeMarkRow_sorted row y sources).1 hmem).mpr
    change row.step + sources.length ≤ _
    omega
  · have hz' := (mem_after_range y sources.length z).mp hnew
    obtain ⟨_, k, hk, hky⟩ := hm.2 y hy
    refine ⟨by omega, ?_⟩
    apply completeMarkRow_target_position hv.1 hs hdis _ hk hky (by omega)
      ((completeMarkRow_core_mem row y sources z).mpr (Or.inr (Or.inr hz')))
    intro x hx
    have hh := hbefore x hx y hy
    omega

end FullMarkedBLP
