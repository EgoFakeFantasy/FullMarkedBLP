import FullMarkedBLP.CompletionSourcePair

namespace FullMarkedBLP

theorem completeMarkRow_high_entry {row : Row} {y x k : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hdis : ∀ z ∈ sources, z ∉ row.core) (hst : ∀ z ∈ sources, z ≤ y)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hx : row.core[k]? = some x) (hhigh : y + sources.length < x) :
    (completeMarkRow row y sources).core[k + 2 * sources.length]? = some x := by
  have hf : sources.filter (· < x) = sources := by
    apply List.filter_eq_self.mpr
    intro z hz
    have hh := hst z hz
    simp; omega
  have htf : (((List.range sources.length).map (fun i => y + 1 + i)).filter (· < x)) =
      (List.range sources.length).map (fun i => y + 1 + i) := by
    apply List.filter_eq_self.mpr
    intro z hz
    have hh := (mem_after_range y sources.length z).mp hz
    simp; omega
  have hrank := completeMarkRow_rank (hc.imp (fun h => Nat.ne_of_lt h)) hs hdis hst ht (x := x)
  simp only [hf, htf, List.length_map, List.length_range, sorted_rank_at_index hc hx] at hrank
  have hm := (completeMarkRow_core_mem row y sources x).mpr
    (Or.inl (List.mem_iff_getElem?.mpr ⟨k, hx⟩))
  have hg := sorted_get_at_rank (completeMarkRow_sorted row y sources).1 hm
  have he : k + sources.length + sources.length = k + 2 * sources.length := by omega
  simpa only [hrank, he] using hg

theorem completeMarkRow_later_pair {row : Row} {y z x k : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hdis : ∀ w ∈ sources, w ∉ row.core)
    (ht : ∀ w, y < w → w ≤ y + sources.length → w ∉ row.core)
    (hk : row.step ≤ k) (hz : row.core[k]? = some z)
    (hx : row.core[k - row.step]? = some x)
    (hxy : x ≤ y) (hbelow : ∀ w ∈ sources, w < x)
    (hhigh : y + sources.length < z) :
    (completeMarkRow row y sources).core[k + 2 * sources.length]? = some z ∧
      (completeMarkRow row y sources).core[k + 2 * sources.length -
        (completeMarkRow row y sources).step]? = some x := by
  have hst : ∀ w ∈ sources, w ≤ y := by intro w hw; have := hbelow w hw; omega
  refine ⟨completeMarkRow_high_entry hc hs hdis hst ht hz hhigh, ?_⟩
  have he : k + 2 * sources.length - (completeMarkRow row y sources).step =
      k - row.step + sources.length := by
    change _ - (row.step + sources.length) = _; omega
  rw [he]
  exact completeMarkRow_middle_entry hc hs hdis ht hx hxy hbelow

theorem completion_later_markTrace {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y z x k : Nat} {row : Row} {sources xs : List Nat}
    (hr : rowAt a r = some row) (hzr : z < r) (hm : z ∈ row.marks)
    (hk : row.step ≤ k) (hz : row.core[k]? = some z)
    (hx : row.core[k - row.step]? = some x) (htrace : Trace a x z xs)
    (hs : sources.Nodup) (hdis : ∀ w ∈ sources, w ∉ row.core)
    (ht : ∀ w, y < w → w ≤ y + sources.length → w ∉ row.core)
    (hxy : x ≤ y) (hbelow : ∀ w ∈ sources, w < x)
    (hhigh : y + sources.length < z) :
    MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r z xs := by
  have hp := completeMarkRow_later_pair (valid r row hr).1 hs hdis ht hk hz hx hxy hbelow hhigh
  have hnm : z ∉ sources := by
    intro hh
    have hb := hbelow z hh
    omega
  have hmark : z ∈ (completeMarkRow row y sources).marks := by
    simp only [completeMarkRow, mem_canonicalColumns, List.mem_append, List.mem_filter]
    exact Or.inl ⟨hm, by simp [hnm]⟩
  refine ⟨completeMarkRow row y sources, k + 2 * sources.length, x,
    rowAt_set_self hr, hmark, ?_, hp.1, hp.2, ?_⟩
  · change row.step + sources.length ≤ _; omega
  · exact trace_prefix valid htrace hzr (fun i hi => (rowAt_set_other hr (by omega : i ≠ r)).symm)

end FullMarkedBLP
