import FullMarkedBLP.CompletionLaterMark

namespace FullMarkedBLP

theorem completeMarkRow_earlier_pair {row : Row} {y z x k : Nat} {sources : List Nat}
    (hc : row.core.Pairwise (· < ·)) (hs : sources.Nodup)
    (hdis : ∀ w ∈ sources, w ∉ row.core)
    (ht : ∀ w, y < w → w ≤ y + sources.length → w ∉ row.core)
    (hk : row.step ≤ k) (hz : row.core[k]? = some z)
    (hx : row.core[k - row.step]? = some x)
    (hxz : x ≤ z) (hzy : z ≤ y) (hgap : ∀ w ∈ sources, x < w ∧ w < z) :
    (completeMarkRow row y sources).core[k + sources.length]? = some z ∧
      (completeMarkRow row y sources).core[k + sources.length -
        (completeMarkRow row y sources).step]? = some x := by
  refine ⟨completeMarkRow_middle_entry hc hs hdis ht hz hzy (fun w hw => (hgap w hw).2), ?_⟩
  have he : k + sources.length - (completeMarkRow row y sources).step = k - row.step := by
    change _ - (row.step + sources.length) = _; omega
  rw [he]
  apply completeMarkRow_low_entry hc hs hdis _ ht hx (by omega)
    (fun w hw => (hgap w hw).1)
  intro w hw
  have hh := (hgap w hw).2
  omega

theorem completion_earlier_markTrace {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y z x k : Nat} {row : Row} {sources xs : List Nat}
    (hr : rowAt a r = some row) (hzr : z < r) (hm : z ∈ row.marks)
    (hk : row.step ≤ k) (hz : row.core[k]? = some z)
    (hx : row.core[k - row.step]? = some x) (htrace : Trace a x z xs)
    (hs : sources.Nodup) (hdis : ∀ w ∈ sources, w ∉ row.core)
    (ht : ∀ w, y < w → w ≤ y + sources.length → w ∉ row.core)
    (hxz : x ≤ z) (hzy : z ≤ y) (hgap : ∀ w ∈ sources, x < w ∧ w < z) :
    MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r z xs := by
  have hp := completeMarkRow_earlier_pair (valid r row hr).1 hs hdis ht hk hz hx hxz hzy hgap
  have hnm : z ∉ sources := by intro hh; have := (hgap z hh).2; omega
  have hmark : z ∈ (completeMarkRow row y sources).marks := by
    simp only [completeMarkRow, mem_canonicalColumns, List.mem_append, List.mem_filter]
    exact Or.inl ⟨hm, by simp [hnm]⟩
  refine ⟨completeMarkRow row y sources, k + sources.length, x,
    rowAt_set_self hr, hmark, ?_, hp.1, hp.2, ?_⟩
  · change row.step + sources.length ≤ _; omega
  · exact trace_prefix valid htrace hzr (fun i hi => (rowAt_set_other hr (by omega : i ≠ r)).symm)

/-- Explicit interval cases suffice for preserving every old marked trace. -/
theorem completion_old_markTrace {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y z x k : Nat} {row : Row} {sources xs : List Nat}
    (hr : rowAt a r = some row) (hzr : z < r) (hm : z ∈ row.marks)
    (hk : row.step ≤ k) (hz : row.core[k]? = some z)
    (hx : row.core[k - row.step]? = some x) (htrace : Trace a x z xs)
    (hs : sources.Nodup) (hdis : ∀ w ∈ sources, w ∉ row.core)
    (ht : ∀ w, y < w → w ≤ y + sources.length → w ∉ row.core)
    (hcases : (x ≤ z ∧ z ≤ y ∧ ∀ w ∈ sources, x < w ∧ w < z) ∨
      (x ≤ y ∧ y + sources.length < z ∧ ∀ w ∈ sources, w < x)) :
    MarkTrace (a.set (r - 1) (completeMarkRow row y sources)) r z xs := by
  rcases hcases with ⟨hxz, hzy, hg⟩ | ⟨hxy, hhigh, hb⟩
  · exact completion_earlier_markTrace valid hr hzr hm hk hz hx htrace hs hdis ht hxz hzy hg
  · exact completion_later_markTrace valid hr hzr hm hk hz hx htrace hs hdis ht hxy hb hhigh

end FullMarkedBLP
