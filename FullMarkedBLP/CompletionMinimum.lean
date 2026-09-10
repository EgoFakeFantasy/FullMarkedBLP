import FullMarkedBLP.CompletionOtherCertificate

namespace FullMarkedBLP

theorem completeMarkRow_preserves_minimum {row : Row} {owner y minimum : Nat}
    {sources : List Nat} (hv : row.CoreValid owner) (hm : row.core.head? = some minimum)
    (hy : minimum ≤ y) (hs : ∀ x ∈ sources, minimum ≤ x) :
    (completeMarkRow row y sources).core.head? = some minimum := by
  have hmem := (completeMarkRow_core_mem row y sources minimum).mpr
    (Or.inl (List.mem_of_head? hm))
  have hlow : ∀ x ∈ (completeMarkRow row y sources).core, minimum ≤ x := by
    intro x hx
    rcases (completeMarkRow_core_mem row y sources x).mp hx with hx | hx | hx
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      exact core_head_le_entry hv hm hi
    · exact hs x hx
    · omega
  have hf : ((completeMarkRow row y sources).core.filter (· < minimum)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have := hlow x hx
    simpa using (not_lt.mpr this)
  have hh := sorted_get_at_rank (completeMarkRow_sorted row y sources).1 hmem
  rw [hf] at hh
  simpa only [List.length_nil, List.head?_eq_getElem?] using hh

end FullMarkedBLP

