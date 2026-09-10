import FullMarkedBLP.CompletionMarks

namespace FullMarkedBLP

theorem completeMarkRow_low_entry {row : Row} {y x k : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hdis : ∀ z ∈ sources, z ∉ row.core) (hst : ∀ z ∈ sources, z ≤ y)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hx : row.core[k]? = some x) (hxy : x ≤ y)
    (habove : ∀ z ∈ sources, x < z) :
    (completeMarkRow row y sources).core[k]? = some x := by
  have hf : sources.filter (· < x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro z hz
    have hh := habove z hz
    simp; omega
  have htf : (((List.range sources.length).map (fun i => y + 1 + i)).filter (· < x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro z hz
    have hh := (mem_after_range y sources.length z).mp hz
    simp; omega
  have hrank := completeMarkRow_rank (hc.imp (fun h => Nat.ne_of_lt h)) hs hdis hst ht (x := x)
  simp only [hf, htf, List.length_nil, Nat.add_zero, sorted_rank_at_index hc hx] at hrank
  have hm := (completeMarkRow_core_mem row y sources x).mpr
    (Or.inl (List.mem_iff_getElem?.mpr ⟨k, hx⟩))
  simpa only [hrank] using sorted_get_at_rank (completeMarkRow_sorted row y sources).1 hm

theorem completeMarkRow_targets_entry {row : Row} {y k : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hdis : ∀ z ∈ sources, z ∉ row.core)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hy : row.core[k]? = some y) (hbelow : ∀ z ∈ sources, z < y)
    {j : Nat} (hj : j ≤ sources.length) :
    (completeMarkRow row y sources).core[k + sources.length + j]? = some (y + j) := by
  induction j with
  | zero => simpa using completeMarkRow_middle_entry hc hs hdis ht hy (Nat.le_refl y) hbelow
  | succ j ih =>
    have he := ih (by omega)
    have hm : y + j + 1 ∈ (completeMarkRow row y sources).core :=
      (completeMarkRow_core_mem row y sources _).mpr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    simpa [Nat.add_assoc] using sorted_consecutive_entry (completeMarkRow_sorted row y sources).1 he hm

/-- The completed old target retains its original source and exact trace. -/
theorem completion_current_markTrace {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y k x : Nat} {row : Row} {sources xs : List Nat}
    (hr : rowAt a r = some row) (hyr : y < r) (hm : y ∈ row.marks)
    (hk : row.step ≤ k) (hy : row.core[k]? = some y)
    (hx : row.core[k - row.step]? = some x) (hxy : x ≤ y) (htrace : Trace a x y xs)
    (hs : sources.Nodup) (hdis : ∀ z ∈ sources, z ∉ row.core)
    (ht : ∀ z, y < z → z ≤ y + sources.length → z ∉ row.core)
    (hgap : ∀ z ∈ sources, x < z ∧ z < y) :
    MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r y xs := by
  have hbelow : ∀ z ∈ sources, z < y := fun z hz => (hgap z hz).2
  have hnm : y ∉ sources := by intro hh; have := hbelow y hh; omega
  have hmark : y ∈ (completeMarkRow row y sources).marks := by
    simp only [completeMarkRow, mem_canonicalColumns, List.mem_append, List.mem_filter]
    exact Or.inl ⟨hm, by simp [hnm]⟩
  refine ⟨completeMarkRow row y sources, k + sources.length, x,
    rowAt_set_self hr, hmark, ?_, ?_, ?_, ?_⟩
  · change row.step + sources.length ≤ _; omega
  · exact completeMarkRow_middle_entry (valid r row hr).1 hs hdis ht hy (Nat.le_refl y) hbelow
  · have he : k + sources.length - (completeMarkRow row y sources).step = k - row.step := by
      change _ - (row.step + sources.length) = _; omega
    rw [he]
    exact completeMarkRow_low_entry (valid r row hr).1 hs hdis
      (fun z hz => Nat.le_of_lt (hbelow z hz)) ht hx hxy (fun z hz => (hgap z hz).1)
  · exact trace_prefix valid htrace hyr (fun i hi => (rowAt_set_other hr (by omega : i ≠ r)).symm)

end FullMarkedBLP
