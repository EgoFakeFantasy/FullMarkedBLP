import FullMarkedBLP.CompletionSemanticCore

namespace FullMarkedBLP

/-- All old core-to-core edges satisfy the paired insertion interval cases;
the source comparisons follow from actual elementary edge equations. -/
theorem rankRealization_completion_old_intervals {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r y p k x z : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (hpy : p ≤ y) (hk : row.step ≤ k) (hz : row.core[k]? = some z)
    (hx : row.core[k - row.step]? = some x)
    (bounds : ∀ u ∈ sources, u ≤ a.length + 1)
    (beforeOwner : y + sources.length < r)
    (targetGap : ∀ u, y < u → u ≤ y + sources.length → u ∉ row.core)
    (packet : ∀ u ∈ sources, rankOrdinalAction (embedding r) (theta u) =
      theta (y + 1 + (sources.filter (· < u)).length)) :
    (x ≤ z ∧ z ≤ y ∧ ∀ u ∈ sources, x < u ∧ u < z) ∨
    (x ≤ y ∧ y + sources.length < z ∧ ∀ u ∈ sources, u < x) := by
  have hv := h.valid r row hr
  have hb := (rowAt_bounds hr).2
  have hxb := core_entry_le_owner hv (List.mem_of_getElem? hx)
  have hzb := core_entry_le_owner hv (List.mem_of_getElem? hz)
  have hxp := step_source_le_p hv hz hx hp
  have hpz := target_position_after_p hv hk hz hp
  have oldEdge : rankOrdinalAction (embedding r) (theta x) = theta z := by
    apply h.edges r row hr (k - row.step) x z (full_entry_of_core hx)
    simpa only [Nat.sub_add_cancel hk] using (full_entry_of_core (owner := r) hz)
  by_cases hzy : z ≤ y
  · refine Or.inl ⟨by omega, hzy, ?_⟩
    intro u hu
    have hi : (sources.filter (· < u)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨u, hu, by simp⟩
    have hxu : theta x < theta u := (rankOrdinalAction_lt_iff (embedding r) _ _).mp (by
      rw [oldEdge, packet u hu]
      exact h.increasing _ _ (by omega) (by omega))
    have hup := rankRealization_edge_source_below_p h hr hp (bounds u hu) (by omega) (packet u hu)
    exact ⟨(rankRealization_column_lt_iff h (by omega) (bounds u hu)).mp hxu, by omega⟩
  · have hhigh : y + sources.length < z := by
      by_contra hn
      exact targetGap z (by omega) (by omega) (List.mem_of_getElem? hz)
    refine Or.inr ⟨by omega, hhigh, ?_⟩
    intro u hu
    have hi : (sources.filter (· < u)).length < sources.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨u, hu, by simp⟩
    have hux : theta u < theta x := (rankOrdinalAction_lt_iff (embedding r) _ _).mp (by
      rw [packet u hu, oldEdge]
      exact h.increasing _ _ (by omega) (by omega))
    exact (rankRealization_column_lt_iff h (bounds u hu) (by omega)).mp hux

/-- Every old core-to-core edge retains an exact pair of new column positions. -/
theorem rankRealization_completion_old_core_pairs {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r y p k x z : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row) (hp : row.p = some p)
    (hpy : p ≤ y) (hk : row.step ≤ k) (hz : row.core[k]? = some z)
    (hx : row.core[k - row.step]? = some x)
    (hs : sources.Nodup) (hdis : ∀ u ∈ sources, u ∉ row.core)
    (bounds : ∀ u ∈ sources, u ≤ a.length + 1)
    (beforeOwner : y + sources.length < r)
    (targetGap : ∀ u, y < u → u ≤ y + sources.length → u ∉ row.core)
    (packet : ∀ u ∈ sources, rankOrdinalAction (embedding r) (theta u) =
      theta (y + 1 + (sources.filter (· < u)).length)) :
    ∃ j, (completeMarkRow row y sources).core[j]? = some x ∧
      (completeMarkRow row y sources).core[j + (completeMarkRow row y sources).step]? = some z := by
  have hv := h.valid r row hr
  rcases rankRealization_completion_old_intervals h hr hp hpy hk hz hx bounds beforeOwner targetGap packet with
    ⟨hxz, hzy, hgap⟩ | ⟨hxy, hhigh, hbelow⟩
  · obtain ⟨ht, hsx⟩ := completeMarkRow_earlier_pair hv.1 hs hdis targetGap hk hz hx hxz hzy hgap
    refine ⟨k - row.step, ?_, ?_⟩
    · convert hsx using 1 <;> simp only [completeMarkRow] <;> congr 1 <;> omega
    · convert ht using 1 <;> simp only [completeMarkRow] <;> congr 1 <;> omega
  · obtain ⟨ht, hsx⟩ := completeMarkRow_later_pair hv.1 hs hdis targetGap hk hz hx hxy hbelow hhigh
    refine ⟨k - row.step + sources.length, ?_, ?_⟩
    · convert hsx using 1 <;> simp only [completeMarkRow] <;> congr 1 <;> omega
    · convert ht using 1 <;> simp only [completeMarkRow] <;> congr 1 <;> omega

/-- The implicit final edge is retained when e lies before the target gap. -/
theorem completeMarkRow_endpoint_pair {row : Row} {r y e : Nat} {sources : List Nat}
    (hv : row.CoreValid r) (he : row.e = some e) (hey : e ≤ y)
    (hs : sources.Nodup) (hdis : ∀ u ∈ sources, u ∉ row.core)
    (targetGap : ∀ u, y < u → u ≤ y + sources.length → u ∉ row.core)
    (below : ∀ u ∈ sources, u < e) :
    ∃ j, ((completeMarkRow row y sources).full r)[j]? = some e ∧
      ((completeMarkRow row y sources).full r)[j + (completeMarkRow row y sources).step]? = some (r + 1) := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hv.2.2.2.1, hroom.le] using he
  have hentry := completeMarkRow_middle_entry hv.1 hs hdis targetGap hei hey below
  have hl := completeMarkRow_length (hv.1.imp (fun hh => Nat.ne_of_lt hh)) hs hdis
    (fun u hu => (below u hu).le.trans hey) targetGap
  refine ⟨row.core.length - row.step + sources.length, full_entry_of_core hentry, ?_⟩
  have hi : row.core.length - row.step + sources.length + (completeMarkRow row y sources).step =
      (completeMarkRow row y sources).core.length := by
    rw [hl]
    change row.core.length - row.step + sources.length + (row.step + sources.length) = _
    omega
  rw [hi]
  simp [Row.full]

end FullMarkedBLP


