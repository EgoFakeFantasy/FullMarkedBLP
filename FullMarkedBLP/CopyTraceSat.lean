import FullMarkedBLP.ExpansionSat

namespace FullMarkedBLP

theorem trace_internal_predecessors {a : Pattern} {s y : Nat} {xs : List Nat}
    (ht : Trace a s y xs) :
    ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
      predecessor a parent = some child := by
  induction ht with
  | stop => simp
  | @next y z tail hsy hp ht ih =>
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons child rest =>
      cases rest with
      | nil => simp
      | cons next rest =>
        have he : child = z := by simpa using trace_head ht
        subst child
        intro parent child hm
        simp only [List.dropLast_cons_cons, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hm
        rcases hm with he | hm
        · obtain ⟨he1, he2⟩ := Prod.mk.inj he
          subst parent; subst child
          exact hp
        · exact ih parent child hm

/-- Entry-state Sat witnesses for all eligible internal factors of a word in
    the copied region. No current +1 guard is needed for this transport. -/
theorem shortCopy_trace_internal_sat {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (hcopy : shortCopy a = some b)
    {s y : Nat} {xs : List Nat} (ht : Trace b s y xs)
    (hregion : ∀ factor ∈ xs.dropLast, a.length ≤ factor) :
    ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
      ∃ row, rowAt b parent = some row ∧ row.p = some child ∧
        (row.core.length ≤ 2 * row.step →
          ∃ e er v, row.e = some e ∧ rowAt b e = some er ∧ er.b = some v ∧ v ≤ child) := by
  intro parent child hedge
  have hp := trace_internal_predecessors ht parent child hedge
  obtain ⟨row, hr, hrp⟩ := Option.bind_eq_some_iff.mp hp
  have hchild : child ∈ xs.dropLast := List.mem_of_mem_tail (List.of_mem_zip hedge).2
  exact ⟨row, hr, hrp, fun hel => shortCopy_internal_sat valid hs hcopy hr hrp (hregion child hchild) hel⟩

theorem shortCopy_trace_sat_of_terminal {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (hcopy : shortCopy a = some b)
    {s y terminal : Nat} {xs : List Nat} (ht : Trace b s y xs)
    (hf : fromRight xs 2 = some terminal) (hterminal : a.length ≤ terminal) :
    ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
      ∃ row, rowAt b parent = some row ∧ row.p = some child ∧
        (row.core.length ≤ 2 * row.step →
          ∃ e er v, row.e = some e ∧ rowAt b e = some er ∧ er.b = some v ∧ v ≤ child) := by
  apply shortCopy_trace_internal_sat valid hs hcopy ht
  intro factor hfactor
  have hb := trace_factor_ge_terminal (shortCopy_preserves_coreValid valid hcopy) ht hf hfactor
  omega

end FullMarkedBLP

