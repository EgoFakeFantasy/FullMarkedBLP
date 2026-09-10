import FullMarkedBLP.CompletionGeometry

namespace FullMarkedBLP

theorem completeMarkRow_rank {row : Row} {y x : Nat} {sources : List Nat}
    (hc : row.core.Nodup) (hs : sources.Nodup)
    (hdis : ∀ z ∈ sources, z ∉ row.core) (hst : ∀ z ∈ sources, z ≤ y)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core) :
    ((completeMarkRow row y sources).core.filter (· < x)).length =
      (row.core.filter (· < x)).length + (sources.filter (· < x)).length +
      (((List.range sources.length).map (fun i => y + 1 + i)).filter (· < x)).length := by
  change ((canonicalColumns _).filter _).length = _
  rw [canonical_filter_length (completeMarkRow_inputs_nodup hc hs hdis hst ht)]
  simp only [List.filter_append, List.length_append]

theorem completeMarkRow_middle_entry {row : Row} {y x k : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hdis : ∀ z ∈ sources, z ∉ row.core)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hx : row.core[k]? = some x) (hxy : x ≤ y)
    (hbelow : ∀ z ∈ sources, z < x) :
    (completeMarkRow row y sources).core[k + sources.length]? = some x := by
  have hst : ∀ z ∈ sources, z ≤ y := by intro z hz; have := hbelow z hz; omega
  have hf : sources.filter (· < x) = sources :=
    List.filter_eq_self.mpr (fun z hz => by simpa using hbelow z hz)
  have htf : (((List.range sources.length).map (fun i => y + 1 + i)).filter (· < x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro z hz
    have hb := (mem_after_range y sources.length z).mp hz
    simp; omega
  have hrank := completeMarkRow_rank (hc.imp (fun h => Nat.ne_of_lt h)) hs hdis hst ht (x := x)
  simp only [hf, htf, List.length_nil, Nat.add_zero, sorted_rank_at_index hc hx] at hrank
  have hm := (completeMarkRow_core_mem row y sources x).mpr
    (Or.inl (List.mem_iff_getElem?.mpr ⟨k, hx⟩))
  simpa only [hrank] using sorted_get_at_rank (completeMarkRow_sorted row y sources).1 hm

/-- Sources inserted below p and targets above it leave the p-value unchanged. -/
theorem completeMarkRow_p {row : Row} {owner y p : Nat} {sources : List Nat}
    (hv : row.CoreValid owner) (hp : row.p = some p)
    (hs : sources.Nodup) (hdis : ∀ z ∈ sources, z ∉ row.core)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hpy : p ≤ y) (hbelow : ∀ z ∈ sources, z < p) :
    (completeMarkRow row y sources).p = some p := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have he := completeMarkRow_middle_entry hv.1 hs hdis ht hi hpy hbelow
  have hst : ∀ z ∈ sources, z ≤ y := by intro z hz; have := hbelow z hz; omega
  have hl := completeMarkRow_length (hv.1.imp (fun h => Nat.ne_of_lt h)) hs hdis hst ht
  have hstep : (completeMarkRow row y sources).step = row.step + sources.length := rfl
  have hidx : row.core.length + 2 * sources.length - (row.step + sources.length + 1) =
      row.core.length - (row.step + 1) + sources.length := by omega
  simpa [Row.p, fromRight, hl, hstep, hidx,
    show row.step + sources.length + 1 ≤ row.core.length + 2 * sources.length by omega] using he

end FullMarkedBLP
